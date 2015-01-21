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
eval env (List (Atom "begin": l: ls)) = (eval env l) >>= (\v -> case v of { (error@(Error _)) -> return error; otherwise -> eval env (List (Atom "begin": ls))})
eval env (List (Atom "begin":[])) = return (List [])
eval env lam@(List (Atom "lambda":(List formals):body:[])) = return lam

-- if function
eval env (List (Atom "if" : cond : conseq : alt : [])) =
        eval env cond >>= (\t -> funcaoIf env (t : conseq : alt : []))

eval env (List(Atom "if" : cond: conseq:[]))=
        eval env cond >>= (\t-> funcaoIfSemElse env (t:conseq:[]))


-- let function
eval env (List (Atom "let" : List attributions : exp : []))
    = lambda env parameters exp values
    where
        (parameters, values) = splitPairs attributions


-- set! function 
eval env (List(Atom "set!": args)) = funcaoSet env args

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
    (maybe (Error "variable does not exist.") 
           id (Map.lookup var (union env s) -- TIVEMOS QUE TROCAR A ORDEM AQUI DOS PARAMETROS
    ), s))


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
defineVar env id val = 
  ST (\s -> let (ST f)    = eval env val
                (result, newState) = f s
            in (result, (insert id result newState))
     )


-- The maybe function yields a value of type b if the evaluation of 
-- its third argument yields Nothing. In case it yields Just x, maybe
-- applies its second argument f to x and yields (f x) as its result.
-- maybe :: b -> (a -> b) -> Maybe a -> b
apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal
apply env func args =  
                  case (Map.lookup func  (trace (show (env)) env)  ) of
                      Just (Native f) -> return (f args)
                      otherwise -> 
                        (stateLookup env func >>= \res -> 
                          case res of 
                            List (Atom "lambda" : List formals : body:l) -> lambda env formals body args                              
                            otherwise -> return (Error "not a function.")
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
          $ insert "+"              (Native numericSum) 
          $ insert "*"              (Native numericMult)
          $ insert "-"              (Native numericSub) 
          $ insert "car"            (Native car)           
          $ insert "cdr"            (Native cdr)
          $ insert "<"              (Native lt)
          $ insert ">"              (Native gt)
          $ insert "<="             (Native lte)
          $ insert ">="             (Native gte)
          $ insert "="              (Native eq)
          $ insert "quotient"       (Native divisao)
          $ insert "modulo"         (Native modulo)
          $ insert "cons"           (Native cons)
          $ insert ";"              (Native comment)
            empty

type StateT = Map String LispVal

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
                 else Error "not a number."
numericSub l = numericBinOp (-) l

-- We have not implemented division. Also, notice that we have not 
-- addressed floating-point numbers.

numericBinOp :: (Integer -> Integer -> Integer) -> [LispVal] -> LispVal
numericBinOp op args = if onlyNumbers args 
                       then Number $ foldl1 op $ Prelude.map unpackNum args 
                       else Error "not a number."
                       


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



lt :: [LispVal] -> LispVal
lt ((Number a):(Number b):[]) = Bool ((<) a b)

gt :: [LispVal] -> LispVal
gt ((Number a):(Number b):[]) = Bool ((>) a b)

lte :: [LispVal] -> LispVal
lte ((Number a):(Number b):[]) = Bool ((<=) a b)

gte :: [LispVal] -> LispVal
gte ((Number a):(Number b):[]) = Bool ((>=) a b)

eq :: [LispVal] -> LispVal
eq ((Number a):(Number b):[]) = Bool ((==) a b)

divisao :: [LispVal] -> LispVal
divisao ((Number a):(Number b):[]) = Number (a `div` b)

modulo :: [LispVal] -> LispVal
modulo ((Number a):(Number b):[]) = Number (a `mod` b)


funcaoIf :: StateT -> [LispVal] -> StateTransformer LispVal
funcaoIf env (((Bool cond)):conseq:alt:[]) 
  | cond   = eval env conseq
  | otherwise = eval env alt
funcaoIf env l = return $ Error "Wrong number of arguments (funcaoIf)"


funcaoIfSemElse :: StateT -> [LispVal] -> StateTransformer LispVal
funcaoIfSemElse env ((Bool cond):conseq:[]) 
  | cond = eval env conseq
  | otherwise = return (String "unspecified") 

splitPairs :: [LispVal] -> ([LispVal], [LispVal])
splitPairs [] = ([], [])
splitPairs ((List (id:val:[])):xs) = (id:ids, val:vals)
    where (ids, vals) = splitPairs xs



--defineVar env id val = 
--  ST (\s -> let (ST f)    = eval env val
--                (result, newState) = f s
--            in (result, (insert id result newState))
--  )

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

comment :: [LispVal] -> LispVal
comment _ = (trace (show ("entrou no comentário")) List[])


-----------------------------------------------------------
--                     main FUNCTION                     --
-----------------------------------------------------------

showResult :: (LispVal, StateT) -> String
showResult (val, defs) = show val ++ "\n" ++ show (toList defs) ++ "\n"

getResult :: StateTransformer LispVal -> (LispVal, StateT)
getResult (ST f) = f empty -- we start with an empty state. 

main :: IO ()
main = do args <- getArgs
          putStr $ showResult $ getResult $ eval environment $ readExpr $ concat $ (trace (show(args)) args) 
          
