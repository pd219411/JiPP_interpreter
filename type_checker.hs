import System.IO ( stdin, hGetContents )

import LexCredo
import ParCredo
import SkelCredo
import PrintCredo
import AbsCredo

import ErrM


import qualified Data.Map
import qualified Control.Monad.State
--------------------------------
data TypeInformation =
	DeducedNone |
	DeducedError [String] |
	DeducedType Type
	deriving (Eq,Ord,Show)

deduceFromType :: Type -> TypeInformation
deduceFromType type' = DeducedType type'

type Location = Int
type FunctionTypeInformation = (Type, [Type])
type FunctionsEnvironment = Data.Map.Map Ident FunctionTypeInformation
type VariablesEnvironment = Data.Map.Map Ident Location
type LocationValues = Data.Map.Map Location Type

data TypeCheckerState =
	TypeCheckerState {
		functions :: FunctionsEnvironment,
		variables :: VariablesEnvironment,
		locations :: LocationValues
	}
	deriving (Eq,Ord,Show)

initialState :: TypeCheckerState
initialState =
	TypeCheckerState {
		functions = Data.Map.empty,
		variables = Data.Map.empty,
		locations = Data.Map.empty
	}

type Semantics a = Control.Monad.State.State TypeCheckerState a
-- albo StateT St (Reader Env) a
-- albo Monada = ReaderT Env (StateT St Identity)

getTypeFromLocation :: LocationValues -> Location -> TypeInformation
getTypeFromLocation m l =
	let ret = Data.Map.lookup l m in
	case ret of
		Nothing -> DeducedError ["Unknown location"]
		Just v -> DeducedType v

getType :: TypeCheckerState -> Ident -> TypeInformation
getType state identifier@(Ident string) =
	let ret = Data.Map.lookup identifier (variables state) in
	case ret of
		Nothing -> DeducedError ["Unknown identifier: " ++ string]
		Just v -> getTypeFromLocation (locations state) v

nextLocation :: VariablesEnvironment -> Location
nextLocation e =
	if Data.Map.null e
	then 0
	else (maximum (Data.Map.elems e)) + 1

addFunction :: TypeCheckerState -> Ident -> FunctionTypeInformation -> TypeCheckerState
addFunction state identifier info = --let ret = Data.Map.lookup identifier (functions state) in
	TypeCheckerState {
		functions = (Data.Map.insert identifier info (functions state)),
		variables = (variables state),
		locations = (locations state)
	}

getFunction :: TypeCheckerState -> Ident -> Maybe FunctionTypeInformation
getFunction state identifier =
	Data.Map.lookup identifier (functions state)

addVariable :: TypeCheckerState -> Ident -> Type -> TypeCheckerState
addVariable state identifier type' = --TODO: what if one exists on this level
	let new_location = (nextLocation (variables state)) in
	TypeCheckerState {
		functions = (functions state),
		variables = (Data.Map.insert identifier new_location (variables state)),
		locations = (Data.Map.insert new_location type' (locations state))
	}

typeOperationSame :: TypeInformation -> TypeInformation -> TypeInformation
typeOperationSame type1 type2 =
	if type1 == type2
	then type1
	else DeducedError ["type combo error add " ++ (show type1)]

typeOperationToBoolean :: TypeInformation -> TypeInformation -> TypeInformation
typeOperationToBoolean type1 type2 =
	if type1 == type2
	then DeducedType TBoolean
	else DeducedError ["type combo error less " ++ (show type1)]

typeStatement :: TypeInformation -> TypeInformation -> TypeInformation
typeStatement DeducedNone type' = type'
typeStatement type' DeducedNone = type'
typeStatement (DeducedError m1) (DeducedError m2) = DeducedError (m1 ++ m2)
typeStatement type1 type2  = (DeducedError ["TODO deduction"])

genericListEval :: (a -> Semantics e) -> [a] -> Semantics [e]
genericListEval evaluator abstraction_list =
		case abstraction_list of
		[] -> return []
		(abstraction:xs) -> do
			head <- (evaluator abstraction)
			tail <- (genericListEval evaluator xs)
			return ([head] ++ tail)

eval :: Expression -> Semantics TypeInformation

eval (EAssignment identifier expression) = do
	return DeducedNone --TODO

eval (ELess expression1 expression2) = do
	type1 <- eval expression1
	type2 <- eval expression2
	return (typeOperationToBoolean type1 type2)

eval (EAdd expression1 expression2) = do
	type1 <- eval expression1
	type2 <- eval expression2
	return (typeOperationSame type1 type2)

eval (ECall identifier@(Ident string) args) = do
	state <- Control.Monad.State.get
	case (getFunction state identifier) of
		Nothing -> return (DeducedError ["Unknown function identifier: " ++ string])
		Just info -> do
			types <- (genericListEval eval args)
			return (checkFunctionCall (snd info) types)
			--return (DeducedError [(show types)])

eval (EVariable identifier) = do
	state <- Control.Monad.State.get
	return (getType state identifier)

eval (EBoolean boolean) = do
	return (DeducedType TBoolean)

eval (EInteger integer) = do
	return (DeducedType TInt)


checkFunctionCall :: [Type] -> [TypeInformation] -> TypeInformation
checkFunctionCall declaration_info args_info =
	let number_of_declared_args = (length declaration_info) in
	let number_of_provided_args = (length args_info) in
	if (number_of_declared_args /= number_of_provided_args)
	then DeducedError ["Bad number of arguments. Declared: " ++ (show number_of_declared_args) ++ " provided: " ++ (show number_of_provided_args)]
	else checkArgsList declaration_info args_info

checkArgsList :: [Type] -> [TypeInformation] -> TypeInformation
checkArgsList [] [] = DeducedNone
checkArgsList (x:xs) (y:ys) =
	case y of
		(DeducedType type') ->
			if type' /= x
			then DeducedError ["Argument type mismatch."]
			else checkArgsList xs ys
		_ -> DeducedError ["Argument of unexpected type."]


evalDeclaration :: Declaration -> Semantics TypeInformation
evalDeclaration (Declaration type' identifier) = do
--	state <- Control.Monad.State.get
--	Control.Monad.State.put (addVariable state identifier type')
	Control.Monad.State.modify (\state -> addVariable state identifier type')
	return (DeducedType type')

evalStatement :: Statement -> Semantics TypeInformation
evalStatement (SDeclaration declaration) = do
	evalDeclaration declaration

evalStatement (SExpression expression) = do
	eval expression

evalStatement (SBlock statements) = do
	evalStatement (statements !! 0)

evalStatements :: [Statement] -> Semantics TypeInformation
evalStatements [] =
	return DeducedNone
evalStatements (x:xs) = do
	type1 <- evalStatement x
	type2 <-evalStatements xs
	return (typeStatement type1 type2)

typeFromDeclaration :: Declaration -> Type
typeFromDeclaration (Declaration type' identifier) = type'

evalFunction :: Function -> Semantics TypeInformation
evalFunction (Function type' identifier declarations statements) = do
	tmp <- genericListEval evalDeclaration declarations
	Control.Monad.State.modify (\state -> addFunction state identifier (type', map typeFromDeclaration declarations))
	evalStatements statements
	--TODO: clear declarations after use

evalProgram :: Program -> Semantics [TypeInformation]
evalProgram (Program functions) = do
	genericListEval evalFunction functions

checkAST :: Program -> ([TypeInformation], TypeCheckerState)
checkAST ast =
	Control.Monad.State.runState (evalProgram ast) initialState

--execStmt :: Stmt -> IO ()
--execStmt stmt = do
--  let ((), finalState) =  runState (runReaderT (interpret stmt) emptyEnv) initialSt
--  print finalState
---------------------------------

type ParseFunction a = [Token] -> Err a
parseResult :: ParseFunction a -> String -> Err a
parseResult p s = p (myLexer s)

main = do
	--hGetContents stdin >>= run pProgram
	contents <- getContents
	--print contents
	let result = (parseResult pProgram contents)
	print result
	print "================"
	case result of
		Bad s -> do
			print "Parse Failed"
			print s
		Ok tree -> do
			print $ checkAST tree
