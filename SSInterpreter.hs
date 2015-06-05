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

-----------------------------------------------------------
--                      INTERPRETER                      --
-----------------------------------------------------------
eval :: StateT -> LispVal -> StateTransformer LispVal
eval env val@(String _) = return val
eval env val@(Atom var) = stateLookup env var 
eval env val@(Number _) = return val
eval env val@(Bool _) = return val

eval env val@(Comment) = return val

eval env (List [Atom "quote", val]) = return val
eval env (List (Atom "begin":[v])) = eval env v
eval env (List (Atom "begin": l: ls)) = ST $ -- correcao monitor
    (\s ->
        let (ST f) = eval env l
            (result, newState) = f s
        in case result of
            error@(Error _) -> (error, newState)
            otherwise ->
                let (ST f2) = eval (union newState env) (List (Atom "begin" : ls))
                    (result2, newState2) = f2 newState
                in (result2, union newState2 newState)
    )
--eval env (List (Atom "begin": l: ls)) = (eval env l) >>= (\v -> case v of { (error@(Error _)) -> return error; otherwise -> eval env (List (Atom "begin": ls))})
eval env (List (Atom "begin":[])) = return (List [])

eval env (List (Atom "comment":[v])) = eval env Comment
eval env (List (Atom "comment": l: ls)) = (eval env l) >>= (\v -> case v of { (error@(Error _)) -> return error; otherwise -> eval env (List (Atom "comment": ls))})
eval env (List (Atom "comment":[])) = return (Comment)

eval env (List (Atom "set!" : var@(Atom variavel) : expression )) = stateLookup env variavel >>= set env var expression
--(begin (define a (+ 5 2)) (set! a 5))

eval env (List (Atom "let" : List bindings : body : [] )) = lett env bindings body  
-- bindings =((variablei initi) . . . ) init sao expressoes
--runhaskell SSInterpreter.hs "(let ((x 2) (y 3)) (* x y))"


eval env (List (Atom "if" : test : consequent : alternate : [] )) = eval env test >>= iff env [consequent] [alternate]
--runhaskell SSInterpreter.hs "(iff (lt? 2 5) (define a 5) (define a 2))"

--eval env (List (Atom "make-closure":lambda:[]))
eval env lam@(List (Atom "lambda":(List formals):body:[])) = return lam
eval env lam@(List (List (Atom "lambda":(List formals):body:[]):args)) = mapM (eval env) args >>= (lambda env formals body)
eval env (List (Atom "make-closure":lambda:[])) = return (Test lambda env)
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
           id (Map.lookup var (union env s) 
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

lett :: StateT -> [LispVal] -> LispVal -> StateTransformer LispVal
lett env bindings body = ST ( \state -> let 
    ST funcao = eval (envAux (union env state) env bindings) body
    (result, newState) = funcao state
  in (result, state))
  
envAux :: StateT -> StateT -> [LispVal] -> StateT
envAux env oldState [] = oldState
envAux env oldState (( List ((Atom var):value:[])):vars) = envAux env newLoc vars
  where newLoc = insert var (fst (getResult(eval env value))) oldState 


-- The maybe function yields a value of type b if the evaluation of 
-- its third argument yields Nothing. In case it yields Just x, maybe
-- applies its second argument f to x and yields (f x) as its result.
-- maybe :: b -> (a -> b) -> Maybe a -> b
apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal
apply env func args =  
                  case (Map.lookup func env) of
                      Just (Native f)  -> return (f args)
                      otherwise ->
                        (stateLookup env func >>= \res ->
                          case res of
                            (Test closure@(List (Atom "lambda" : List formals : body:l)) envClosure) ->
                              ST $ (\s -> let envs = union envClosure env
                                              (ST f1) = lambda envs formals body args
                                              (result1, newState1) = f1 $ union envs s
                                              interState = intersection newState1 envClosure
                                              (ST f2) = eval interState (List [Atom "define", Atom func, List [Atom "make-closure", closure]])
                                              (result2, newState2) = f2 $ union newState1 $ union env s
                                              newEnv = union (difference newState2 (difference envClosure env)) env 
                                in (result1, newEnv)
                              )
                            List (Atom "lambda" : List formals : body:l) -> lambda env formals body args      
                            otherwise -> return (Error " not a function!")
                        )

{-apply :: StateT -> String -> [LispVal] -> StateTransformer LispVal
apply env func args =  
                  case (Map.lookup func env) of
                      Just (Native f) -> return (f args)
                      otherwise -> 
                        (stateLookup env func >>= \res -> 
                          case res of 
                            List (Atom "lambda":List formals:body:[]) -> lambda env formals body args
                             otherwise -> return (Error "not a function.")
                        )
 -}
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
          $ insert "/"              (Native numericDiv)
          $ insert "mod"            (Native numericMod)       
          $ insert "car"            (Native car)           
          $ insert "cdr"            (Native cdr)
          $ insert "eqv?"           (Native eqv)
          $ insert "lt?"            (Native lt)
          $ insert "cons"           (Native cons)
          $ insert "concatena"       (Native concatena)
      
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
--set :: StateT -> LispVal -> [LispVal] -> StateTransformer LispVal
set env var args (Error t) = return (Error t)
set env var args _ = define env (var:args)

iff env [consequent] [alternate] (Bool True) = eval env consequent
iff env [consequent] [] (Bool False) = return (Atom "")
iff env [consequent] [alternate] (Bool False) = eval env alternate 
--head
car :: [LispVal] -> LispVal
car [List (a:as)] = a
car [DottedList (a:as) _] = a
car ls = Error "invalid list."
--tail
cdr :: [LispVal] -> LispVal
cdr (List (a:as) : ls) = List as
cdr (DottedList (a:[]) c : ls) = c
cdr (DottedList (a:as) c : ls) = DottedList as c
cdr ls = Error "invalid list."

-- ++
concatena :: [LispVal] -> LispVal 
concatena [(List l1), (List l2)] = List (l1++l2)
concatena _ = Error "invalid lists."

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

numericDiv :: [LispVal] -> LispVal
numericDiv [] = Number 0
numericDiv l = numericBinOp (div) l

numericMod :: [LispVal] -> LispVal
numericMod [] = Number 0
numericMod l = numericBinOp (mod) l

numericSub :: [LispVal] -> LispVal
numericSub [] = Error "wrong number of arguments."
-- The following case handles negative number literals.
numericSub [x] = if onlyNumbers [x]
                 then (\num -> (Number (- num))) (unpackNum x)
                 else Error "not a number."
numericSub l = numericBinOp (-) l

eqv :: [LispVal] -> LispVal
eqv ( (Number a): (Number b) : []) = (Bool (a==b))
eqv ( (String a): (String b) : []) = (Bool (a==b))
eqv ( (Bool a): (Bool b) : []) = (Bool (a==b))
eqv ( (Number a): (String b) : []) = Bool False
eqv ( (String a): (Number b) : []) = Bool False
eqv ( (List a) : (List b) : []) =  Bool (eqvList a b)
eqv ( (Number _) : [(List _)] ) = Bool False
eqv ( (List _) : [(Number _)] ) = Bool False
eqv [DottedList a b, DottedList c d] = Bool (eqvDottedList a b c d)

eqvDottedList :: [LispVal] -> LispVal -> [LispVal] -> LispVal -> Bool
eqvDottedList a b c d
 | (eqvList a c) && e =  True
 | otherwise =  False
 where Bool e = (eqv [b, d])

eqvList [] [] =  True
eqvList [] _ =  False
eqvList _ [] =  False
eqvList (a:as) (b:bs) = if c
  then eqvList as bs
  else  False
  where Bool c = (eqv (a:[b])) 

lt :: [LispVal] -> LispVal
lt [] = Error "wrong number of arguments."
lt l = foldAux (<) l

foldAux :: (Integer -> Integer -> Bool) -> [LispVal] -> LispVal
foldAux f [x] =  Error "wrong number of arguments."
foldAux f (x:[e]) = if( f (unpackNum x) (unpackNum e) ) then Bool True else Bool False
foldAux f (x:(e:l)) = if( f (unpackNum x) (unpackNum e) ) then foldAux f (e:l) else Bool False

cons :: [LispVal] -> LispVal
cons [ a, (List b) ] = List (a:b)
cons _ =  Error "invalid arguments."
-- "(difine a (cons 2 (cons 3 '()) ))"

--set :: [LispVal] -> LispVal

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

--como rodar codigos skim
--runhaskell SSInterpreter.hs "código"
