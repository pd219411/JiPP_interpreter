module Interpreter (
interpret
) where

import LexCredo
import ParCredo
import SkelCredo
import PrintCredo
import AbsCredo

import ErrM


import Debug.Trace
import qualified Data.Map
import qualified Data.Maybe
import qualified Control.Monad.State
--------------------------------

data RuntimeValue =
	RuntimeInteger Integer |
	RuntimeBoolean Bool
	deriving (Eq,Ord,Show)

convertBooleanToHaskell :: Boolean -> Bool
convertBooleanToHaskell boolean =
	case boolean of
		ValueFalse -> False
		ValueTrue -> True

type Location = Int
type FunctionRuntimeInformation = Function
type FunctionsEnvironment = Data.Map.Map Ident FunctionRuntimeInformation
type VariablesEnvironment = [Data.Map.Map Ident Location]
type LocationValues = Data.Map.Map Location RuntimeValue

data InterpreterState =
	InterpreterState {
		functions :: FunctionsEnvironment,
		variables :: VariablesEnvironment,
		locations :: LocationValues
	}
	deriving (Eq,Ord,Show)

initialState :: FunctionsEnvironment -> InterpreterState
initialState functions_environment =
	InterpreterState {
		functions = functions_environment,
		variables = [],
		locations = Data.Map.empty
	}

type Runtime a = Control.Monad.State.State InterpreterState a
--type Runtime a = (Control.Monad.State.StateT InterpreterState IO) a


--TODO: copy paste from type chceker
nextLocation :: LocationValues -> Location
nextLocation e =
	if Data.Map.null e
	then 0
	else (maximum (Data.Map.keys e)) + 1

--addFunction :: TypeCheckerState -> Ident -> FunctionTypeInformation -> TypeCheckerState
--addFunction state identifier info = --let ret = Data.Map.lookup identifier (functions state) in
	--TypeCheckerState {
		--functions = (Data.Map.insert identifier info (functions state)),
		--variables = (variables state),
		--locations = (locations state)
	--}

getFunction :: InterpreterState -> Ident -> FunctionRuntimeInformation
getFunction state identifier =
	Data.Maybe.fromJust (Data.Map.lookup identifier (functions state))

--addToVariablesEnvironment :: VariablesEnvironment -> Ident -> Location -> VariablesEnvironment
--addToVariablesEnvironment [] _ _ = error "Adding variable to empty environment stack"
--addToVariablesEnvironment variables@(x:xs) identifier location =
	--(Data.Map.insert identifier location x):xs

addLocationToEnvironment :: VariablesEnvironment -> Ident -> Location -> VariablesEnvironment
addLocationToEnvironment variables@(x:xs) identifier location =
	(Data.Map.insert identifier location x):xs

--allFromVariablesEnvironment :: VariablesEnvironment -> Ident -> Maybe Location
--allFromVariablesEnvironment variables@(x:xs) identifier =
	--let finder block n =
		--case (Data.Map.lookup identifier block) of
			--Nothing -> n
			--Just location -> Just location
	--in foldr (finder) Nothing variables

getLocationFromEnvironment :: VariablesEnvironment -> Ident -> Location
getLocationFromEnvironment variables@(x:xs) identifier =
	let finder block n =
		case (Data.Map.lookup identifier block) of
			Nothing -> n
			Just location -> Just location
	in Data.Maybe.fromJust (foldr (finder) Nothing variables)

--topFromVariablesEnvironment :: VariablesEnvironment -> Ident -> Maybe Location
--topFromVariablesEnvironment variables@(block:xs) identifier =
	--(Data.Map.lookup identifier block)

openBlock :: InterpreterState -> InterpreterState
openBlock state =
	InterpreterState {
		functions = (functions state),
		variables = (Data.Map.empty):(variables state),
		locations = (locations state)
	}

leaveBlock :: InterpreterState -> InterpreterState
leaveBlock state =
	InterpreterState {
		functions = (functions state),
		variables = tail (variables state),
		locations = (locations state)
	}

addVariable :: InterpreterState -> Ident -> RuntimeValue -> InterpreterState
addVariable state identifier value = --TODO: what if one exists on this level
	let new_location = (nextLocation (locations state)) in
	InterpreterState {
		functions = (functions state),
		variables = (addLocationToEnvironment (variables state) identifier new_location),
		locations = (Data.Map.insert new_location value (locations state))
	}

--addIdentifier :: InterpreterState -> Ident -> InterpreterState
--addIdentifier state identifier =
	--InterpreterState {
		--functions = (functions state),
		--variables = (variables state),
		--locations = (Data.Map.insert location value (locations state))
	--}

getValueFromLocation :: LocationValues -> Location -> RuntimeValue
getValueFromLocation locations location =
	Data.Maybe.fromJust (Data.Map.lookup location locations)

getValue :: InterpreterState -> Ident -> RuntimeValue
getValue state identifier =
	let location = getLocationFromEnvironment (variables state) identifier in
	getValueFromLocation (locations state) location

setValue :: InterpreterState -> Ident -> RuntimeValue -> InterpreterState
setValue state identifier value =
	let location = getLocationFromEnvironment (variables state) identifier in
	InterpreterState {
		functions = (functions state),
		variables = (variables state),
		locations = (Data.Map.insert location value (locations state))
	}

--allVariable :: TypeCheckerState -> Ident -> Maybe Type
--allVariable state identifier =
	--let ret = allFromVariablesEnvironment (variables state) identifier in
	--case ret of
		--Nothing -> Nothing
		--Just location -> Just (getTypeFromLocation (locations state) location)

--topVariable :: TypeCheckerState -> Ident -> Maybe Type
--topVariable state identifier =
	--let ret = topFromVariablesEnvironment (variables state) identifier in
	--case ret of
		--Nothing -> Nothing
		--Just location -> Just (getTypeFromLocation (locations state) location)

--typeOperationSame :: TypeInformation -> TypeInformation -> TypeInformation
--typeOperationSame type1 type2 =
	--if type1 == type2
	--then type1
	--else DeducedError ["type combo error add " ++ (show type1)]

--typeOperationToBoolean :: TypeInformation -> TypeInformation -> TypeInformation
--typeOperationToBoolean type1 type2 =
	--if type1 == type2
	--then DeducedType TBoolean
	--else DeducedError ["type combo error less " ++ (show type1)]

--typeStatement :: TypeInformation -> TypeInformation -> TypeInformation
--typeStatement DeducedNone type' = type'
--typeStatement type' DeducedNone = type'
--typeStatement (DeducedError m1) (DeducedError m2) = DeducedError (m1 ++ m2)
--typeStatement type1 type2  = (DeducedError ["TODO deduction"])

--TODO: the same thing as in type_checker
genericListEval :: (a -> Runtime e) -> [a] -> Runtime [e]
genericListEval evaluator abstraction_list =
		case abstraction_list of
		[] -> return []
		(abstraction:xs) -> do
			head <- (evaluator abstraction)
			tail <- (genericListEval evaluator xs)
			return (head:tail)

genericListEvalWithParam :: (a -> b -> Runtime e) -> [a] -> [b] -> Runtime [e]
genericListEvalWithParam evaluator abstraction_list_1 abstraction_list_2@(abstraction_2:ys) =
		case abstraction_list_1 of
		[] -> return []
		(abstraction_1:xs) -> do
			head <- (evaluator abstraction_1 abstraction_2)
			tail <- (genericListEvalWithParam evaluator xs ys)
			return (head:tail)

---------------------------------------

interpretExpression :: Expression -> Runtime RuntimeValue

interpretExpression (ELess expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeBoolean (value1 < value2))

interpretExpression (EAdd expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeInteger (value1 + value2))

interpretExpression (ECall identifier args) = do
	arg_values <- genericListEval interpretExpression args
	state <- Control.Monad.State.get
	interpretFunction (getFunction state identifier) arg_values

interpretExpression (EVariable identifier) = do
	state <- Control.Monad.State.get
	return (getValue state identifier)

interpretExpression (EBoolean boolean) = do
	return (RuntimeBoolean (convertBooleanToHaskell boolean))

interpretExpression (EInteger integer) = do
	return (RuntimeInteger integer)

--checkFunctionCall :: [Type] -> [TypeInformation] -> TypeInformation
--checkFunctionCall declaration_info args_info =
	--let number_of_declared_args = (length declaration_info) in
	--let number_of_provided_args = (length args_info) in
	--if (number_of_declared_args /= number_of_provided_args)
	--then DeducedError ["Bad number of arguments. Declared: " ++ (show number_of_declared_args) ++ " provided: " ++ (show number_of_provided_args)]
	--else checkArgsList declaration_info args_info

--checkArgsList :: [Type] -> [TypeInformation] -> TypeInformation
--checkArgsList [] [] = DeducedNone
--checkArgsList (x:xs) (y:ys) =
	--case y of
		--(DeducedType type') ->
			--if type' /= x
			--then DeducedError ["Argument type mismatch."]
			--else checkArgsList xs ys
		--_ -> DeducedError ["Argument of unexpected type."]

--TODO: maybe we dont need to eval those if in context of function call
--evalDeclaration :: Declaration -> Runtime ()
--evalDeclaration (Declaration type' identifier@(Ident string)) = do
	--state <- Control.Monad.State.get
	--case (topVariable state identifier) of
		--Nothing -> do
			--Control.Monad.State.modify (\state -> addVariable state identifier type')
			--return DeducedNone
		--Just _ -> return (DeducedError ["Redefinition of variable: " ++ string])

interpretStatement :: Statement -> Runtime ()

interpretStatement (SAssignment identifier expression) = do
	value <- interpretExpression expression
	Control.Monad.State.modify (\state -> setValue state identifier value)

interpretStatement (SDeclaration declaration) = do
	return () --evalDeclaration declaration
	--TODO: not sure how we deal with declarations in functions vs in code

interpretStatement (SExpression expression) = do
	interpretExpression expression
	return ()

interpretStatement (SBlock statements) = do
	Control.Monad.State.modify openBlock
	--TODO: we dont have statements interpreter yet
	--temp <- interpretStatements statements
	--genericListEval interpretStatement statements
	Control.Monad.State.modify leaveBlock
	--return temp

interpretStatement (SReturn expression) = do
	value <- interpretExpression expression
	--return value
	return ()

--TODO: what is the result (none or return?)
--interpretStatements :: [Statement] -> Runtime TypeInformation
--interpretStatements [] =
	--return DeducedNone
--interpretStatements (x:xs) = do
	--type1 <- interpretStatement x
	--type2 <- interpretStatements xs
	--return (typeStatement type1 type2)

--typeFromDeclaration :: Declaration -> Type
--typeFromDeclaration (Declaration type' identifier) = type'

interpretArgumentDeclaration :: ArgumentDeclaration -> RuntimeValue -> Runtime ()
interpretArgumentDeclaration (ArgumentDeclaration type' identifier) value =
	Control.Monad.State.modify (\state -> addVariable state identifier value)


interpretFunction :: Function -> [RuntimeValue] -> Runtime RuntimeValue
interpretFunction (Function type' identifier declarations statements) arguments = do
	--Control.Monad.State.liftIO (print $ "Funkcja " ++ (show identifier))
	Control.Monad.State.modify openBlock
	genericListEvalWithParam interpretArgumentDeclaration declarations arguments
	--interpret
	value <- interpretStatement (statements !! 0)
	Control.Monad.State.modify leaveBlock
	--return computed value from statements
	return (RuntimeInteger 1000)


--interpretProgram :: Program -> Runtime RuntimeValue
--interpretProgram (Program functions) = do
	----TODO: it is the same thing as running main() without params
	--genericListEval interpretFunction functions

--checkAST :: Program -> ([[TypeInformation]], TypeCheckerState)
--checkAST ast =
	--Control.Monad.State.runState (evalProgram ast) initialState

interpretProgram :: Program -> Runtime RuntimeValue
interpretProgram (Program functions) = do
	interpretExpression (ECall (Ident "main") [])

generateFunctionsMap :: Program -> Data.Map.Map Ident Function
generateFunctionsMap (Program functions) =
	let add_to_map map function@(Function type' identifier declarations statements) =
		Data.Map.insert identifier function map
	in foldl (add_to_map) Data.Map.empty functions


interpret :: Program -> RuntimeValue
interpret program =
	let (ret, state) = (Control.Monad.State.runState (interpretProgram program) (initialState (generateFunctionsMap program))) in
	ret
