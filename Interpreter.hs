{-# LANGUAGE TypeSynonymInstances, FlexibleInstances #-}
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
type Location = Int

data RuntimeValue =
	RuntimeNone |
	RuntimeInteger Integer |
	RuntimeBoolean Bool |
	RuntimeReference Location
	deriving (Eq,Ord,Show)

convertBooleanToHaskell :: Boolean -> Bool
convertBooleanToHaskell boolean =
	case boolean of
		ValueFalse -> False
		ValueTrue -> True

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

--type Runtime a = Control.Monad.State.State InterpreterState a
--type Runtime a = (Control.Monad.State.StateT InterpreterState IO) a
type Runtime = Control.Monad.State.StateT InterpreterState IO


class Printer p where
	printString :: String -> p ()
	printValue :: Int -> p ()

instance Printer Runtime where
	printString str = Control.Monad.State.liftIO $ putStr str
	printValue i = Control.Monad.State.liftIO $ print i


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
	in (Data.Maybe.fromJust (foldr (finder) Nothing variables))

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

expandLocations :: InterpreterState -> RuntimeValue -> InterpreterState
expandLocations state value =
	let new_location = (nextLocation (locations state)) in
	InterpreterState {
		functions = (functions state),
		variables = (variables state),
		locations = (Data.Map.insert new_location value (locations state))
	}

addVariable :: InterpreterState -> Ident -> RuntimeValue -> InterpreterState
addVariable state identifier value =
	let new_location = (nextLocation (locations state)) in
	let state' = InterpreterState {
		functions = (functions state),
		variables = (addLocationToEnvironment (variables state) identifier new_location),
		locations = (locations state)
	} in
	expandLocations state' value

addArray :: InterpreterState -> Integer -> RuntimeValue -> InterpreterState
addArray state size initial =
	if size > 0
	then (addArray (expandLocations state initial) (size - 1) initial)
	else state

getValueFromLocation :: LocationValues -> Location -> RuntimeValue
getValueFromLocation locations location =
	Data.Maybe.fromJust (Data.Map.lookup location locations)

getValue :: InterpreterState -> Ident -> RuntimeValue
getValue state identifier =
	let location = getLocationFromEnvironment (variables state) identifier in
	getValueFromLocation (locations state) location

setValue :: InterpreterState -> Location -> RuntimeValue -> InterpreterState
setValue state location value =
	InterpreterState {
		functions = (functions state),
		variables = (variables state),
		locations = (Data.Map.insert location value (locations state))
	}

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
genericListEvalWithParam evaluator abstraction_list_1 abstraction_list_2 =
	case abstraction_list_1 of
	[] -> return []
	(abstraction_1:xs) -> do
		first <- (evaluator abstraction_1 (head abstraction_list_2))
		rest <- (genericListEvalWithParam evaluator xs (tail abstraction_list_2))
		return (first:rest)

---------------------------------------

interpretExpression :: Expression -> Runtime RuntimeValue

interpretExpression (EEqual expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeBoolean (value1 == value2))

interpretExpression (ELess expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeBoolean (value1 < value2))

interpretExpression (ELessEqual expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeBoolean (value1 <= value2))

interpretExpression (EAdd expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeInteger (value1 + value2))

interpretExpression (ESub expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeInteger (value1 - value2))

interpretExpression (EMul expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeInteger (value1 * value2))

interpretExpression (EDiv expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeInteger (div value1 value2))

interpretExpression (EMod expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeInteger (mod value1 value2))

interpretExpression (EAnd expression1 expression2) = do
	RuntimeBoolean value1 <- interpretExpression expression1
	RuntimeBoolean value2 <- interpretExpression expression2
	return (RuntimeBoolean (value1 && value2))

interpretExpression (EOr expression1 expression2) = do
	RuntimeBoolean value1 <- interpretExpression expression1
	RuntimeBoolean value2 <- interpretExpression expression2
	return (RuntimeBoolean (value1 || value2))

interpretExpression (ENot expression1) = do
	RuntimeBoolean value1 <- interpretExpression expression1
	return (RuntimeBoolean (not value1))

interpretExpression (ECall identifier args) = do
	arg_values <- genericListEval interpretExpression args
	state <- Control.Monad.State.get
	interpretFunction (getFunction state identifier) arg_values

interpretExpression (EVariable identifier) = do
	state <- Control.Monad.State.get
	return (getValue state identifier)

interpretExpression (EReference lvalue) = do
	state <- Control.Monad.State.get
	location <- interpretLvalue lvalue
	return (RuntimeReference location)

interpretExpression (ELvalue lvalue) = do
	location <- interpretLvalue lvalue
	getValueHelper location

interpretExpression (ENewArray type' size_expression initial_value_expression) = do
	RuntimeInteger size <- interpretExpression size_expression
	value <- interpretExpression initial_value_expression
	state <- Control.Monad.State.get
	let first_location = nextLocation (locations state)
	if ((size < 1) || (size > (1024 * 1024)))
	then do
		fail "Invalid array size"
	else do
		Control.Monad.State.modify (\state -> addArray state size value)
		return (RuntimeReference first_location)

interpretExpression (EBoolean boolean) = do
	return (RuntimeBoolean (convertBooleanToHaskell boolean))

interpretExpression (EInteger integer) = do
	return (RuntimeInteger integer)


interpretLvalue :: Lvalue -> Runtime Location

interpretLvalue (LIdentifier identifier) = do
	state <- Control.Monad.State.get
	return (getLocationFromEnvironment (variables state) identifier)

interpretLvalue (LAddress lvalue) = do
	address <- interpretLvalue lvalue
	RuntimeReference location <- (getValueHelper address)
	return location

interpretLvalue (LIndex identifier expression) = do
	RuntimeInteger index <- interpretExpression expression
	location <- interpretLvalue (LAddress (LIdentifier identifier))
	return (location + (fromIntegral index))
	--evalLvalue (LAddress (LIdentifier identifier))

getValueHelper :: Location -> Runtime RuntimeValue
getValueHelper location = do
	state <- Control.Monad.State.get
	return (getValueFromLocation (locations state) location)


interpretStatement :: Statement -> Runtime RuntimeValue

interpretStatement (SAssignment lvalue expression) = do
	location <- interpretLvalue lvalue
	value <- interpretExpression expression
	Control.Monad.State.modify (\state -> setValue state location value)
	return RuntimeNone

interpretStatement (SBlock statements) = do
	Control.Monad.State.modify openBlock
	temp <- interpretStatements statements
	Control.Monad.State.modify leaveBlock
	return temp

interpretStatement (SDeclaration (VariableDeclaration type' identifier) expression) = do
	value <- interpretExpression expression
	Control.Monad.State.modify (\state -> addVariable state identifier value)
	return RuntimeNone

interpretStatement (SExpression expression) = do
	interpretExpression expression
	return RuntimeNone

interpretStatement (SIfBare expression statements) = do
	RuntimeBoolean condition_value <- interpretExpression expression
	if condition_value
	then interpretStatement (SBlock statements)
	else return RuntimeNone

interpretStatement (SIfElse expression statements1 statements2) = do
	RuntimeBoolean condition_value <- interpretExpression expression
	if condition_value
	then interpretStatement (SBlock statements1)
	else interpretStatement (SBlock statements2)

interpretStatement (SPrint (PrintString string)) = do
	printString string
	return RuntimeNone

interpretStatement (SPrint (PrintInteger expression)) = do
	RuntimeInteger value <- interpretExpression expression
	printString (show value)
	return RuntimeNone

interpretStatement (SReturn expression) = do
	value <- interpretExpression expression
	return value

interpretStatement while@(SWhile expression statements) = do
	RuntimeBoolean condition_value <- interpretExpression expression
	if condition_value
	then do
		value <- interpretStatement (SBlock statements)
		case value of
			RuntimeNone -> interpretStatement while
			_ -> return value
	else return RuntimeNone

interpretStatements :: [Statement] -> Runtime RuntimeValue
interpretStatements [] =
	return RuntimeNone
interpretStatements (x:xs) = do
	value <- interpretStatement x
	case value of
		RuntimeNone -> interpretStatements xs
		_ -> return value
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
	value <- interpretStatements statements
	Control.Monad.State.modify leaveBlock
	return value


interpretProgram :: Program -> Runtime RuntimeValue
interpretProgram (Program functions) = do
	interpretExpression (ECall (Ident "main") [])

generateFunctionsMap :: Program -> Data.Map.Map Ident Function
generateFunctionsMap (Program functions) =
	let add_to_map map function@(Function type' identifier declarations statements) =
		Data.Map.insert identifier function map
	in foldl (add_to_map) Data.Map.empty functions


interpret :: Program -> IO (RuntimeValue, InterpreterState)
interpret program = do
	Control.Monad.State.runStateT (interpretProgram program) (initialState (generateFunctionsMap program))
