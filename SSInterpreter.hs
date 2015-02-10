{-

A basic interpreter for a purely functional subset of Scheme named SkimScheme.
Part of this interpreter has been derived from the "Write Yourself a Scheme in
48 Hours - An Introduction to Haskell through Example", by Jonathan Tang. It
does not implement a number of Scheme's constructs. Moreover, it uses a
different approach to implement mutable state within the language.

The name "SkimScheme" refers to the stripped down nature of this interpreter.
According to the New Oxford American Dictionary, "skim" can mean:

(as a verb) ... read (something) quickly or cursorily so as to note only
the important points.

(as a noun) ... an act of reading something quickly or superficially. 

"skimmed/skim milk" is milk from which the cream has been removed. 

The name emphasizes that we do not want to cover the entire standard, small as
it may be. Instead, we want to focus on some of the important aspects, taking a
language implementer's point of view, with the goal of using it as a teaching
tool. Many, many, many aspects of Scheme standards are not covered (it does not
even support recursion!).

Written by Fernando Castor
Started at: August 28th 2012
Last update: December 17th 2012

-}

module Main where
import System.Environment
import Control.Monad
import Data.Map as Map
import LispVal
import SSParser
import SSPrettyPrinter

import Debug.Trace

-----------------------------------------------------------
--                      INTERPRETER                      --
-----------------------------------------------------------
eval :: StateT -> LispVal -> StateTransformer LispVal
eval env val@(String _) = return val
eval env val@(Atom var) = stateLookup env var 
eval env val@(Number _) = return val
eval env val@(Bool _) = return val
eval env (List [Atom "quote", val]) = return val
eval env (List (Atom "begin":[v])) = eval env v
--eval env (List (Atom "begin": l: ls)) = (eval env l) >>= (\v -> case v of { (error@(Error _)) -> return error; otherwise -> eval env (List (Atom "begin": ls))})
eval env (List (Atom "begin":[])) = ST $ (\s -> (List [], env))

--eval env (List (Atom "begin": l: ls)) = (eval env l) >>= 
--      (\v -> 
--          case v of { 
--              (error@(Error _)) -> return error; 
--              otherwise -> eval env (List (Atom "begin": ls))
--          }
--      )

eval env (List (Atom "begin": l: ls)) = ST $
  (\s ->
    let (ST f) = eval env l
        (result, newState) = f s
    in case result of
    --in case (trace ("\nresult: "++(show (result))) result) of
      (error@(Error _)) -> (error, newState)
      otherwise         -> let envir = (union newState env)
                               --(ST f2) = eval (trace ("\nenvir"++(show (envir))) envir) (List (Atom "begin" : ls))
                               (ST f2) = eval newState (List (Atom "begin" : ls))
                               (result2, newState2) = f2 envir
                            in (result2, (union newState2 newState))
  )


eval env lam@(List (Atom "lambda":(List formals):body:[])) = return lam

eval env (List (Atom "comment" : _)) = return (List [])

-- make-closure function
-- recebe o nome make-closure + funcao lambda (igual a de cima)
-- retorna um lispval com o lambda concatenado com o environment atual
eval env closure@(List(Atom "make-closure" : lam@(List (Atom "lambda" : (List formals) : body : [])) : [])) =
 --return (List (lam : (Environment (trace (show (env)) env)) : []))
 return (List (lam : (Environment env) : []))




--funcaoIf :: StateT -> [LispVal] -> StateTransformer LispVal
--funcaoIf env (((Bool cond)):conseq:alt:[]) 
--  | cond   = eval env conseq
--  | otherwise = eval env alt
--funcaoIf env l = return $ Error "Wrong number of arguments (funcaoIf)"

---- if function
--eval env (List (Atom "if" : cond : conseq : alt : [])) =
--        eval env cond >>= (\t -> funcaoIf env (t : conseq : alt : []))



eval env (List (Atom "if" : cond : conseq : alt : [])) = ST $
  (\s -> let (ST f) = eval env cond
             (result, newState) = f (union env s)
         in 
            case result of
            (Bool condicao) -> if (condicao) then
                                    let (ST f1) = eval (union newState env) conseq
                                        (result1, newState1) = f1 (union newState env)
                                    in (result1, (union newState1 newState))
                                else
                                    let (ST f2) = eval (union newState env) alt
                                        (result2, newState2) = f2 (union newState env)
                                    in (result2, (union newState2 newState))
            otherwise       -> (Error ("Wrong type of arguments"), newState)
    )


eval env (List (Atom "if" : cond : conseq : [])) = ST $
  (\s -> let (ST f) = eval env cond
             (result, newState) = f (union env s)
         in case result of
            (Bool condicao) -> if (condicao) then
                                    let (ST f1) = eval (union newState env) conseq
                                        (result1, newState1) = f1 (union newState env)
                                    in (result1, (union newState1 newState))
                                else
                                    ((Error ("unspecified")), newState)
            otherwise       -> (Error ("Wrong type of arguments"), newState)
  )
------ let function
--eval env (List (Atom "let" : List attributions : exp : []))
--    = lambda env params exp values
--    where
--        (params, values) = splitPairs attributions


eval env (List (Atom "let" : List attributions : exp : []))
    = let params = splitPairs attributions
          avaliaParams = (\(id, expr) -> 
                        let (ST f) = eval env expr
                            (val, newState) = f env 
                         in (id, val))
          envVazio = Map.empty 
          args = Prelude.map avaliaParams params
          inserirNoEnv = (\(Atom f, a) m -> Map.insert f a m)
          letEnv = Prelude.foldr inserirNoEnv envVazio args

      in ST $ (\s -> let (ST f) = eval (union letEnv env) exp
                         (result, newState) = f s
                         finalState = union (difference newState letEnv) env
                     in (result, finalState)
    )


-- set! function 
eval env (List(Atom "set!" : args)) = funcaoSet env args



-- The following line is slightly more complex because we are addressing the
-- case where define is redefined by the user (whatever is the user's reason
-- for doing so. The problem is that redefining define does not have
-- the same semantics as redefining other functions, since define is not
-- stored as a regular function because of its return type.
eval env (List (Atom "define": args)) = maybe (define env args) (\v -> return v) (Map.lookup "define" env)

eval env (List (Atom func : args)) = mapM (eval env) args >>= apply env func 
eval env (Error s)  = return (Error s)
eval env form = return (Error ("Could not eval the special form: " ++ (show form)))


stateLookup :: StateT -> String -> StateTransformer LispVal
stateLookup env var = ST $ 
  (\s -> 
    (maybe (Error ((show var)++" -> variable does not exist. - stateLookup"))
           id (Map.lookup var (union env s)
           --id (Map.lookup (trace ("******     trace...    *********"++(show (union env s))) var) (union env s) -- TIVEMOS QUE TROCAR A ORDEM AQUI DOS PARAMETROS
    ), (union env s)))


-- Because of monad complications, define is a separate function that is not
-- included in the state of the program. This saves  us from having to make
-- every predefined function return a StateTransformer, which would also
-- complicate state management. The same principle applies to set!. We are still
-- not talking about local definitions. That's a completely different
-- beast.
define :: StateT -> [LispVal] -> StateTransformer LispVal
define env [(Atom id), val] = defineVar env id val
define env [(List [Atom id]), val] = defineVar env id val
-- define env [(List l), val]                                       
define env args = return (Error "wrong number of arguments")

-- adicionar um union entre os states pra ele poder pegar as variaveis direito,
-- sem perder as antigas
defineVar env id val = 
  ST (\s -> let (ST f)    = eval env val
                (result, newState) = f s
            --in (result, (insert id result newState))
            in (result, (insert id result (union newState env))) -- ele tem que incluir o novo estado no retorno, mas sem ignorar o antigo
     )


-- The maybe function yields a value of type b if the evaluation of 
-- its third argument yields Nothing. In case it yields Just x, maybe
-- applies its second argument f to x and yields (f x) as its result.
-- maybe :: b -> (a -> b) -> Maybe a -> b
apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal
apply env func args =  
                  case (Map.lookup func env) of
                  --case (Map.lookup (trace (show (func)) func) (trace (show (env)) env)) of
                      Just (Native f) -> return (f args)
                      otherwise -> 
                        (stateLookup env func >>= \res -> 
                          case res of 
                            List (lam@(List (Atom "lambda" : List formals : body : [])) : (Environment localEnv) : []) -> ST $
                                (\s ->
                                    let closureEnv = union localEnv env
                                        (ST f) = lambda closureEnv formals body args
                                        (result, newState) = f $ union closureEnv s
                                        (ST f2) = eval newState (List (Atom "define" : Atom func : (List (Atom "make-closure" : lam : [])) : []))
                                        (result2, newClosureState) = f2 $ union newState $ union env s
                                        finalState = union (difference newClosureState (difference localEnv env)) env
                                    in (result, finalState)
                                )
                            List (Atom "lambda" : List formals : body:l) -> lambda env formals body args                              
                            otherwise -> return (Error ((show res) ++"   not a function."))
                        )
 
-- The lambda function is an auxiliary function responsible for
-- applying user-defined functions, instead of native ones. We use a very stupid 
-- kind of dynamic variable (parameter) scoping that does not even support
-- recursion. This has to be fixed in the project.
lambda :: StateT -> [LispVal] -> LispVal -> [LispVal] -> StateTransformer LispVal
lambda env formals body args = 
  let dynEnv = Prelude.foldr (\(Atom f, a) m -> Map.insert f a m) env (zip formals args)
  in  eval dynEnv body


-- Initial environment of the programs. Maps identifiers to values. 
-- Initially, maps function names to function values, but there's 
-- nothing stopping it from storing general values (e.g., well-known
-- constants, such as pi). The initial environment includes all the 
-- functions that are available for programmers.
environment :: Map String LispVal
environment =   
            insert "number?"        (Native predNumber)
          $ insert "boolean?"       (Native predBoolean)
          $ insert "list?"          (Native predList)

          $ insert "null?"          (Native predNull)

          $ insert "append"         (Native append)
 
           
          $ insert "+"              (Native numericSum) 
          $ insert "-"              (Native numericSub)  
          $ insert "/"              (Native divisao)       
          $ insert "*"              (Native numericMult)
          $ insert "lt?"            (Native lt)
          $ insert "mod"            (Native modulo)
          

          $ insert "eqv?"           (Native eqv)
          $ insert "<"              (Native lt)
          $ insert ">"              (Native gt)

          

          $ insert "<="             (Native lte)
          $ insert ">="             (Native gte)
          $ insert "="              (Native eq)
        
        
          $ insert "cons"           (Native cons)
          $ insert "car"            (Native car)           
          $ insert "cdr"            (Native cdr) 
           
  
            empty

-- type StateT = Map String LispVal

-- StateTransformer is a data type that embodies computations
-- that transform the state of the interpreter (add new (String, LispVal)
-- pairs to the state variable). The ST constructor receives a function
-- because a StateTransformer gets the previous state of the interpreter 
-- and, based on that state, performs a computation that might yield a modified
-- state (a modification of the previous one). 
data StateTransformer t = ST (StateT -> (t, StateT))

instance Monad StateTransformer where
  return x = ST (\s -> (x, s))
  (>>=) (ST m) f = ST (\s -> let (v, newS) = m s
                                 (ST resF) = f v
                             in  resF newS
                      )
    
-----------------------------------------------------------
--          HARDWIRED PREDEFINED LISP FUNCTIONS          --
-----------------------------------------------------------

-- Includes some auxiliary functions. Does not include functions that modify
-- state. These functions, such as define and set!, must run within the
-- StateTransformer monad. 

car :: [LispVal] -> LispVal
car [List (a:as)] = a
car [DottedList (a:as) _] = a
car ls = Error "invalid list."

cdr :: [LispVal] -> LispVal
cdr (List (a:as) : ls) = List as
cdr (DottedList (a:[]) c : ls) = c
cdr (DottedList (a:as) c : ls) = DottedList as c
cdr ls = Error "invalid list."

predNumber :: [LispVal] -> LispVal
predNumber (Number _ : []) = Bool True
predNumber (a:[]) = Bool False
predNumber ls = Error "wrong number of arguments."

predBoolean :: [LispVal] -> LispVal
predBoolean (Bool _ : []) = Bool True
predBoolean (a:[]) = Bool False
predBoolean ls = Error "wrong number of arguments."

predList :: [LispVal] -> LispVal
predList (List _ : []) = Bool True
predList (a:[]) = Bool False
predList ls = Error "wrong number of arguments."

numericSum :: [LispVal] -> LispVal
numericSum [] = Number 0
numericSum l = numericBinOp (+) l

numericMult :: [LispVal] -> LispVal
numericMult [] = Number 1
numericMult l = numericBinOp (*) l

numericSub :: [LispVal] -> LispVal
numericSub [] = Error "wrong number of arguments."
-- The following case handles negative number literals.
numericSub [x] = if onlyNumbers [x]
                 then (\num -> (Number (- num))) (unpackNum x)
                 else Error "not a number (sub)."
numericSub l = numericBinOp (-) l

-- We have not implemented division. Also, notice that we have not 
-- addressed floating-point numbers.

numericBinOp :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal
numericBinOp op args = if onlyNumbers args 
                       then Number $ foldl1 op $ Prelude.map unpackNum args 
                       else Error "not a number (numericBinOp)."
                       


onlyNumbers :: [LispVal] -> Bool
onlyNumbers [] = True
onlyNumbers (Number n:ns) = onlyNumbers ns
onlyNumbers ns = False             
                       
unpackNum :: LispVal -> Integer
unpackNum (Number n) = n
--- unpackNum a = ... -- Should never happen!!!!




----------------------------------------------------------------------
----------------------------------------------------------------------
--------------------------  OUR FUNCTIONS  ---------------------------
----------------------------------------------------------------------
----------------------------------------------------------------------

-- TO DO:
-- if         OK
-- recursion  
-- let        OK
-- set!       OK
-- comment    OK
-- cons       OK
-- lt?        OK
-- /          OK
-- mod        OK
-- eqv?       
-- clausuras  

lt :: [LispVal] -> LispVal
lt ((Number a):(Number b):[]) = Bool ((<) a b)
lt ((Number a):(Number b):ls) = if (<) a b then
                                  lt ((Number b):ls)
                                else
                                  Bool False
lt _ = Error ("Wrong number or type of arguments")


gt :: [LispVal] -> LispVal
gt ((Number a):(Number b):[]) = Bool ((>) a b)
gt ((Number a):(Number b):ls) = if (>) a b then
                                  gt ((Number b):ls)
                                else
                                  Bool False
gt _ = Error ("Wrong number or type of arguments")


lte :: [LispVal] -> LispVal
lte ((Number a):(Number b):[]) = Bool ((<=) a b)
lte ((Number a):(Number b):ls) = if (<=) a b then
                                  lte ((Number b):ls)
                                else
                                  Bool False
lte _ = Error ("Wrong number or type of arguments")


gte :: [LispVal] -> LispVal
gte ((Number a):(Number b):[]) = Bool ((>=) a b)
gte ((Number a):(Number b):ls) = if (>=) a b then
                                  gte ((Number b):ls)
                                else
                                  Bool False
gte _ = Error ("Wrong number or type of arguments")


eq :: [LispVal] -> LispVal
eq ((Number a):(Number b):[]) = Bool ((==) a b)
eq ((Number a):(Number b):ls) = if (==) a b then
                                  eq ((Number b):ls)
                                else
                                  Bool False
eq _ = Error ("Wrong number or type of arguments")


evalBool :: (LispVal -> LispVal -> Bool) -> LispVal -> LispVal -> Bool
evalBool op l1 l2 = op l1 l2


divisao :: [LispVal] -> LispVal
divisao ((Number a):(Number b):[]) = Number (a `div` b)
divisao ((Error _):l) = Error ("Wrong number or type of arguments")
divisao l = if (zerofree (tail l)) then
              numericBinOp (div) l
            else
              Error ("Division by zero")

zerofree :: [LispVal] -> Bool
zerofree [] = True
zerofree ((Number a):as) = if a == 0 then
                             False
                           else
                             zerofree as

modulo :: [LispVal] -> LispVal
modulo ((Number a):(Number b):[]) = Number (a `mod` b)
modulo _ = Error ("Wrong number or type of arguments")


predNull :: [LispVal] -> LispVal
predNull ([List []]) = Bool True
predNull (List _ : []) = Bool False
predNull (a:[]) = (trace (show a) (Bool False))
predNull ls = Error "wrong number of arguments."



funcaoIf :: StateT -> [LispVal] -> StateTransformer LispVal
funcaoIf env (((Bool cond)):conseq:alt:[]) 
  | cond   = eval env conseq
  | otherwise = eval env alt
funcaoIf env l = return $ Error "Wrong number of arguments (funcaoIf)"

funcaoIfSemElse :: StateT -> [LispVal] -> StateTransformer LispVal
funcaoIfSemElse env ((Bool cond):conseq:[]) 
  | cond = eval env conseq
  | otherwise = return (String "unspecified") 

splitPairs :: [LispVal] -> [(LispVal, LispVal)]
splitPairs [] = []
splitPairs ((List (id:val:[])):xs) = (id, val) : rest
    where rest = splitPairs xs



-- igual a funcao define, mas na hora de inserir, checa se ja tem
funcaoSet :: StateT -> [LispVal] -> StateTransformer LispVal
funcaoSet env [(Atom id), val] = ST $
  (\s -> let (ST f) = eval env val
             (result, newState) = f s
         in
            if (Map.member id newState) then 
              (result, (insert id result newState))
            else 
              (Error ("variable does not exist."), newState)
  )

-- funcaoSet env (Atom var) lv | Map.member var env = ST $ (ins -> ((Error ("Unspecified")), ins))
--                      | otherwise = return (Error("Variable is not defined in this scope"))
--                        where ins = Map.insert var lv env 
--funcaoSet _ _ _ = return (Error ("do it right"))               

--attribute :: a -> StateTransformer LispVal
--attribute _ = return (Error ("unspecified"))

cons :: [LispVal] -> LispVal
cons (a:[List b]) = List (a:b)
cons (a:b)        = List (a:b)
cons l            = Error ("Wrong number of arguments")

eqv :: [LispVal] -> LispVal
eqv ((Bool a):(Bool b):[])     = Bool (a == b)
eqv ((Number a):(Number b):[]) = Bool (a == b)
eqv ((List []):(List []):[])   = Bool (True) -- duas listas vazias, passa #t
eqv ((String a):(String b):[]) = Bool (a == b)
eqv ((Atom a):(Atom b):[])     = Bool (a == b)
--eqv l                         = Bool ((trace (show(l)) False))
eqv list@((List a): (List b):[])    = (trace (show(list)) eqvList a b) 

eqvList :: [LispVal] -> [LispVal] -> LispVal
eqvList [] []         = (Bool True)
eqvList _  []         = (Bool False)
eqvList [] _          = (Bool False)
eqvList (a:as) (b:bs) = if unpackBool (eqv [a]:[b]) then
                          eqvList as bs
                        else 
                          (Bool False)

unpackBool :: [LispVal] -> Bool
unpackBool ((Bool b):[]) = b




--append :: [LispVal] -> LispVal
--append [] = List []
--append [List l] = List l
--append ((List l):(List k):d) = List (l ++ k) 
--          where (List k) = append (k++d)
--append _ = Error $ "Wrong number of arguments"

append :: [LispVal] -> LispVal
append [] = List []
append [List l] = List l
append ((List l):ls) = let ka = append ls
                       in case ka of
                       (List k) -> List (l ++ k)
                       otherwise -> (trace ("****ka: "++(show ka)++"\n****ls: "++(show ls)) Error (""))
append _ = Error $ "Wrong number of arguments"


--append :: [LispVal] -> LispVal
--append [] = (trace (show "\nappend\n") (List []))
--append [List l] = (trace (show "\nappend\n") (List l))
--append ((List l):ls) = List (l ++ k) where (List k) = append (trace (show "\nappend\n") ls)
--append _ = Error $ "Wrong number of arguments"


-----------------------------------------------------------
--                     main FUNCTION                     --
-----------------------------------------------------------

showResult :: (LispVal, StateT) -> String
showResult (val, defs) = show val ++ "\n" ++ show (toList defs) ++ "\n"

getResult :: StateTransformer LispVal -> (LispVal, StateT)
getResult (ST f) = f empty -- we start with an empty state. 

main :: IO ()
main = do args <- getArgs
          putStr $ showResult $ getResult $ eval environment $ readExpr $ concat $ args
          
