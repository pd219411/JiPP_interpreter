import System.IO ( stdin, hGetContents )

import LexCredo
import ParCredo
import SkelCredo
import PrintCredo
import AbsCredo

import ErrM

import Interpreter


import Debug.Trace
import qualified Data.Map
import qualified Data.Maybe
import qualified Control.Monad.State
--------------------------------
data TypeInformation =
	DeducedNone |
	DeducedError [String] |
	DeducedType Type
	deriving (Eq,Ord,Show)

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
--stateAfterBlockLeft :: TypeCheckerState -> TypeCheckerState -> TypeCheckerState
--stateAfterBlockLeft state_on_enter state_on_leave =
--	TypeCheckerState {
--		functions = (functions state_on_leave),
--		variables = (variables state_on_enter),
--		locations = (locations state_on_enter)
--	}

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

genericListEval :: (a -> Semantics e) -> [a] -> Semantics [e]
genericListEval evaluator abstraction_list =
		case abstraction_list of
		[] -> return []
		(abstraction:xs) -> do
			head <- (evaluator abstraction)
			tail <- (genericListEval evaluator xs)
			return (head:tail)

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

evalStatement (SDeclaration declaration) = do
	evalVariableDeclaration declaration

evalStatement (SExpression expression) = do
	evalExpression expression

evalStatement (SBlock statements) = do
	Control.Monad.State.modify openBlock
	temp <- evalStatements statements
	--genericListEval evalStatement statements
	Control.Monad.State.modify leaveBlock
	return temp

evalStatements :: [Statement] -> Semantics TypeInformation
evalStatements [] =
	return DeducedNone
evalStatements (x:xs) = do
	type1 <- evalStatement x
	type2 <- evalStatements xs
	return (typeStatement type1 type2)

typeFromDeclaration :: ArgumentDeclaration -> Type
typeFromDeclaration (ArgumentDeclaration type' identifier) = type'

evalFunction :: Function -> Semantics [TypeInformation]
evalFunction (Function type' identifier@(Ident string) declarations statements) = do
	state_on_enter <- Control.Monad.State.get
	case (getFunction state_on_enter identifier) of
		Just info -> return [(DeducedError ["Redefinition of function: " ++ string])]
		Nothing -> do
			Control.Monad.State.modify (\state -> addFunction state identifier (type', map typeFromDeclaration declarations))
			Control.Monad.State.modify openBlock
			temp1 <- genericListEval evalArgumentDeclaration declarations
			temp2 <- genericListEval evalStatement statements
			Control.Monad.State.modify leaveBlock
			return (temp1 ++ temp2) --TODO: check returns etc.

evalProgram :: Program -> Semantics [[TypeInformation]]
evalProgram (Program functions) = do
	--TODO: check if program contains function main()
	genericListEval evalFunction functions

checkAST :: Program -> ([[TypeInformation]], TypeCheckerState)
checkAST ast =
	Control.Monad.State.runState (evalProgram ast) initialState


generateFunctionsMap :: Program -> Data.Map.Map Ident Function
generateFunctionsMap (Program functions) =
	let add_to_map map function@(Function type' identifier declarations statements) =
		Data.Map.insert identifier function map
	in foldl (add_to_map) Data.Map.empty functions

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
			print (checkAST tree)
			print "================ FUNCTIONS:"
			print (generateFunctionsMap tree)
			--if no errors interpret
