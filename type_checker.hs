import System.IO ( stdin, hGetContents )

import LexCredo
import ParCredo
import SkelCredo
import PrintCredo
import AbsCredo

import ErrM

import Interpreter


import qualified Data.Map
import qualified Data.Maybe
import qualified Control.Monad.State

--------------------------------
data TypeInformation =
	DeducedNone |
	DeducedError [String] |
	DeducedType Type
	deriving (Eq,Ord,Show)

typeIsError :: TypeInformation -> Bool
typeIsError info =
	case info of
		DeducedError _ -> True
		_ -> False

typeIsOfType :: TypeInformation -> Type -> Bool
typeIsOfType info type'=
	case info of
		DeducedType type' -> True
		_ -> False

type Location = Int
type FunctionTypeInformation = (Type, [Type])
type FunctionsEnvironment = Data.Map.Map Ident FunctionTypeInformation
type VariablesEnvironment = [Data.Map.Map Ident Location]
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
		variables = [],
		locations = Data.Map.empty
	}

type Semantics a = Control.Monad.State.State TypeCheckerState a

nextLocation :: LocationValues -> Location
nextLocation e =
	if Data.Map.null e
	then 0
	else (maximum (Data.Map.keys e)) + 1

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

addToVariablesEnvironment :: VariablesEnvironment -> Ident -> Location -> VariablesEnvironment
addToVariablesEnvironment [] _ _ = error "Adding variable to empty environment stack"
addToVariablesEnvironment variables@(x:xs) identifier location =
	(Data.Map.insert identifier location x):xs

allFromVariablesEnvironment :: VariablesEnvironment -> Ident -> Maybe Location
allFromVariablesEnvironment variables@(x:xs) identifier =
	let finder block n =
		case (Data.Map.lookup identifier block) of
			Nothing -> n
			Just location -> Just location
	in foldr (finder) Nothing variables

topFromVariablesEnvironment :: VariablesEnvironment -> Ident -> Maybe Location
topFromVariablesEnvironment variables@(block:xs) identifier =
	(Data.Map.lookup identifier block)

openBlock :: TypeCheckerState -> TypeCheckerState
openBlock state =
	TypeCheckerState {
		functions = (functions state),
		variables = (Data.Map.empty):(variables state),
		locations = (locations state)
	}

leaveBlock :: TypeCheckerState -> TypeCheckerState
leaveBlock state =
	TypeCheckerState {
		functions = (functions state),
		variables = tail (variables state),
		locations = (locations state)
	}

addVariable :: TypeCheckerState -> Ident -> Type -> TypeCheckerState
addVariable state identifier type' = --TODO: what if one exists on this level
	let new_location = (nextLocation (locations state)) in
	TypeCheckerState {
		functions = (functions state),
		variables = (addToVariablesEnvironment (variables state) identifier new_location),
		locations = (Data.Map.insert new_location type' (locations state))
	}

getTypeFromLocation :: LocationValues -> Location -> Type
getTypeFromLocation locations location =
	Data.Maybe.fromJust (Data.Map.lookup location locations)

allVariable :: TypeCheckerState -> Ident -> Maybe Type
allVariable state identifier =
	let ret = allFromVariablesEnvironment (variables state) identifier in
	case ret of
		Nothing -> Nothing
		Just location -> Just (getTypeFromLocation (locations state) location)

topVariable :: TypeCheckerState -> Ident -> Maybe Type
topVariable state identifier =
	let ret = topFromVariablesEnvironment (variables state) identifier in
	case ret of
		Nothing -> Nothing
		Just location -> Just (getTypeFromLocation (locations state) location)




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

errorFold :: [TypeInformation] -> String -> TypeInformation
errorFold infos error_message =
	if (any typeIsError infos)
	then (DeducedError [error_message])
	else DeducedNone


genericListEval :: (a -> Semantics e) -> [a] -> Semantics [e]
genericListEval evaluator abstraction_list =
		case abstraction_list of
		[] -> return []
		(abstraction:xs) -> do
			head <- (evaluator abstraction)
			tail <- (genericListEval evaluator xs)
			return (head:tail)

---------------------------------------------------------

evalExpression :: Expression -> Semantics TypeInformation

evalExpression (ELess expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	return (typeOperationToBoolean type1 type2)

evalExpression (EAdd expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	return (typeOperationSame type1 type2)

evalExpression (ECall identifier@(Ident string) args) = do
	state <- Control.Monad.State.get
	case (getFunction state identifier) of
		Nothing -> return (DeducedError ["Unknown function identifier: " ++ string])
		Just info -> do
			types <- (genericListEval evalExpression args)
			return (checkFunctionCall (snd info) types)

evalExpression (EVariable identifier@(Ident string)) = do
	state <- Control.Monad.State.get
	case (topVariable state identifier) of --TODO: check out blocks too
		Nothing -> return (DeducedError ["Unknown identifier: " ++ string])
		Just type' -> return (DeducedType type')

evalExpression (EBoolean boolean) = do
	return (DeducedType TBoolean)

evalExpression (EInteger integer) = do
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
			then DeducedError ["Argument type mismatch"]
			else checkArgsList xs ys
		_ -> DeducedError ["Argument of unexpected type"]


declareHelper :: Type -> Ident -> Semantics TypeInformation
declareHelper type' identifier@(Ident string) = do
	state <- Control.Monad.State.get
	case (topVariable state identifier) of
		Nothing -> do
			Control.Monad.State.modify (\state -> addVariable state identifier type')
			return DeducedNone
		Just _ -> return (DeducedError ["Redefinition of variable: " ++ string])

evalArgumentDeclaration :: ArgumentDeclaration -> Semantics TypeInformation
evalArgumentDeclaration (ArgumentDeclaration type' identifier) =
	declareHelper type' identifier

evalVariableDeclaration :: VariableDeclaration -> Semantics TypeInformation
evalVariableDeclaration (VariableDeclaration type' identifier) =
	declareHelper type' identifier

evalStatement :: Statement -> Semantics TypeInformation

evalStatement (SAssignment identifier@(Ident string) expression) = do
	state <- Control.Monad.State.get
	case (allVariable state identifier) of
		Nothing -> return (DeducedError ["Unknown identifier: " ++ string])
		Just variable_type -> do
			expression_info <- evalExpression expression
			case expression_info of
				DeducedType expression_type -> if variable_type == expression_type
					then return DeducedNone
					else return (DeducedError ["Assignment type mismatch: " ++ (show variable_type) ++ " = " ++ (show expression_type)])
				_ -> return expression_info

evalStatement (SBlock statements) = do
	Control.Monad.State.modify openBlock
	temp <- evalStatements statements
	Control.Monad.State.modify leaveBlock
	return temp

evalStatement (SDeclaration declaration) = do
	evalVariableDeclaration declaration

evalStatement (SExpression expression) = do
	_ <- evalExpression expression
	return DeducedNone

evalStatement (SIfBare expression statements) = do
	expression_info <- evalExpression expression
	--TODO: open block
	statements_info <- evalStatements statements
	if (typeIsOfType expression_info TBoolean)
	then return (errorFold [statements_info] "if contains an error")
	else return (DeducedError ["Condition not a boolean"])

evalStatement (SIfElse expression statements1 statements2) = do
	expression_info <- evalExpression expression
	--TODO: open block
	info1 <- evalStatements statements1
	info2 <- evalStatements statements2
	if (typeIsOfType expression_info TBoolean)
	--then return (errorFold [statements_info] "if contains an error")
	then return (typeOperationSame info1 info2)
	else return (DeducedError ["Condition not a boolean"])

evalStatement (SReturn expression) = do
	evalExpression expression

evalStatements :: [Statement] -> Semantics TypeInformation
evalStatements [] =
	return DeducedNone
evalStatements [statement] =
	evalStatement statement
evalStatements (x:xs) = do
	info <- evalStatement x
	case info of
		DeducedNone -> evalStatements xs
		DeducedType _ -> return (DeducedError ["Ureachable code"])
		_ -> return info

typeFromDeclaration :: ArgumentDeclaration -> Type
typeFromDeclaration (ArgumentDeclaration type' identifier) = type'

evalFunction :: Function -> Semantics TypeInformation
evalFunction (Function type' identifier@(Ident string) declarations statements) = do
	state_on_enter <- Control.Monad.State.get
	case (getFunction state_on_enter identifier) of
		Just _ -> return (DeducedError ["Redefinition of function: " ++ string])
		Nothing -> do
			Control.Monad.State.modify (\state -> addFunction state identifier (type', map typeFromDeclaration declarations))
			Control.Monad.State.modify openBlock
			temp1 <- genericListEval evalArgumentDeclaration declarations
			temp2 <- evalStatements statements
			Control.Monad.State.modify leaveBlock
			--TODO: CHECK RETURN EXISTS AND HAS FINE TYPE!
			return (errorFold (temp2:temp1) "Function contains an error")

isMain :: Function -> Bool
isMain (Function _ (Ident string) declarations statements) =
	string == "main" && declarations == []

evalProgram :: Program -> Semantics TypeInformation
evalProgram (Program functions) = do
	case (any isMain functions) of
		False -> return (DeducedError ["main() does not exist"])
		True -> do
			functions_info <- genericListEval evalFunction functions
			return (errorFold functions_info "Program contains an error")

checkAST :: Program -> (TypeInformation, TypeCheckerState)
checkAST ast =
	Control.Monad.State.runState (evalProgram ast) initialState

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
			let (compile_info, state) = (checkAST tree)
			print compile_info
			if compile_info == DeducedNone
			then do
				print "=============== LETS DO THIS:"
				print (interpret tree)
			else do
				print "Fail"
