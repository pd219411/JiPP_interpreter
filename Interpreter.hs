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
--data TypeInformation =
	--DeducedNone |
	--DeducedError [String] |
	--DeducedType Type
	--deriving (Eq,Ord,Show)

data RuntimeValue =
	RuntimeInteger Int |
	RuntimeBoolean Bool

convertBooleanToHaskell :: Boolean -> Bool
convertBooleanToHaskell boolean =
	case boolean of
		ValueFalse -> False
		ValueTrue -> True

type Location = Int
type FunctionTypeInformation = (Type, [Type]) --TODO: informations needed to call this
type FunctionsEnvironment = Data.Map.Map Ident FunctionTypeInformation
type VariablesEnvironment = [Data.Map.Map Ident Location]
type LocationValues = Data.Map.Map Location RuntimeValue

data InterpreterState =
	InterpreterState {
		functions :: FunctionsEnvironment,
		variables :: VariablesEnvironment,
		locations :: LocationValues
	}
	deriving (Eq,Ord,Show)

initialState :: InterpreterState
initialState =
	InterpreterState {
		functions = Data.Map.empty,
		variables = [],
		locations = Data.Map.empty
	}

type Runtime a = Control.Monad.State.State InterpreterState a


--nextLocation :: LocationValues -> Location
--nextLocation e =
	--if Data.Map.null e
	--then 0
	--else (maximum (Data.Map.keys e)) + 1

--addFunction :: TypeCheckerState -> Ident -> FunctionTypeInformation -> TypeCheckerState
--addFunction state identifier info = --let ret = Data.Map.lookup identifier (functions state) in
	--TypeCheckerState {
		--functions = (Data.Map.insert identifier info (functions state)),
		--variables = (variables state),
		--locations = (locations state)
	--}

--getFunction :: TypeCheckerState -> Ident -> Maybe FunctionTypeInformation
--getFunction state identifier =
	--Data.Map.lookup identifier (functions state)

--addToVariablesEnvironment :: VariablesEnvironment -> Ident -> Location -> VariablesEnvironment
--addToVariablesEnvironment [] _ _ = error "Adding variable to empty environment stack"
--addToVariablesEnvironment variables@(x:xs) identifier location =
	--(Data.Map.insert identifier location x):xs

--allFromVariablesEnvironment :: VariablesEnvironment -> Ident -> Maybe Location
--allFromVariablesEnvironment variables@(x:xs) identifier =
	--let finder block n =
		--case (Data.Map.lookup identifier block) of
			--Nothing -> n
			--Just location -> Just location
	--in foldr (finder) Nothing variables

getLocationFromEnvironment :: VariablesEnvironment -> Ident -> Maybe Location
getLocationFromEnvironment variables@(x:xs) identifier =
	let finder block n =
		case (Data.Map.lookup identifier block) of
			Nothing -> n
			Just location -> Just location
	in foldr (finder) Nothing variables

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

--addVariable :: TypeCheckerState -> Ident -> Type -> TypeCheckerState
--addVariable state identifier type' = --TODO: what if one exists on this level
	--let new_location = (nextLocation (locations state)) in
	--TypeCheckerState {
		--functions = (functions state),
		--variables = (addToVariablesEnvironment (variables state) identifier new_location),
		--locations = (Data.Map.insert new_location type' (locations state))
	--}

getValueFromLocation :: LocationValues -> Location -> RuntimeValue
getValueFromLocation locations location =
	Data.Maybe.fromJust (Data.Map.lookup location locations)

getValue :: Runtime -> Ident -> RuntimeValue
getValue state identifier =
	let location = getLocationFromEnvironment (variables state) identifier in
	getValueFromLocation location (locations state)

setValue :: Runtime -> Ident -> RuntimeValue -> Runtime
setValue runtime identifier value =
	let location = getLocationFromEnvironment (variables runtime) identifier in
	InterpreterState {
		functions = (functions runtime),
		variables = (variables runtime),
		locations = (Data.Map.insert location value (locations runtime))
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

--genericListEval :: (a -> Semantics e) -> [a] -> Semantics [e]
--genericListEval evaluator abstraction_list =
		--case abstraction_list of
		--[] -> return []
		--(abstraction:xs) -> do
			--head <- (evaluator abstraction)
			--tail <- (genericListEval evaluator xs)
			--return (head:tail)

---------------------------------------

interpretExpression :: Expression -> Runtime RuntimeValue

interpretExpression (ELess expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeBoolean value1 < value2)

interpretExpression (EAdd expression1 expression2) = do
	RuntimeInteger value1 <- interpretExpression expression1
	RuntimeInteger value2 <- interpretExpression expression2
	return (RuntimeInteger value1 + value2)

interpretExpression (ECall identifier@(Ident string) args) = do
	return (RuntimeInteger 500)
	--TODO: interpret structure containing function code
	--state <- Control.Monad.State.get
	--case (getFunction state identifier) of
		--Nothing -> return (DeducedError ["Unknown function identifier: " ++ string])
		--Just info -> do
			--types <- (genericListEval evalExpression args)
			--return (checkFunctionCall (snd info) types)

interpretExpression (EVariable identifier) = do
	state <- Control.Monad.State.get
	return (getValue state identifier)

interpretExpression (EBoolean boolean) = do
	return (RuntimeBoolean convertBooleanToHaskell boolean)

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

interpretStatement (SBlock statements) = do
	Control.Monad.State.modify openBlock
	temp <- interpretStatements statements
	--genericListEval interpretStatement statements
	Control.Monad.State.modify leaveBlock
	return temp

interpretStatements :: [Statement] -> Semantics TypeInformation
interpretStatements [] =
	return DeducedNone
interpretStatements (x:xs) = do
	type1 <- interpretStatement x
	type2 <- interpretStatements xs
	return (typeStatement type1 type2)

typeFromDeclaration :: Declaration -> Type
typeFromDeclaration (Declaration type' identifier) = type'

evalFunction :: Function -> Semantics [TypeInformation]
evalFunction (Function type' identifier@(Ident string) declarations statements) = do
	state_on_enter <- Control.Monad.State.get
	case (getFunction state_on_enter identifier) of
		Just info -> return [(DeducedError ["Redefinition of function: " ++ string])]
		Nothing -> do
			Control.Monad.State.modify (\state -> addFunction state identifier (type', map typeFromDeclaration declarations))
			Control.Monad.State.modify openBlock
			temp1 <- genericListEval evalDeclaration declarations
			temp2 <- genericListEval interpretStatement statements
			Control.Monad.State.modify leaveBlock
			return (temp1 ++ temp2) --TODO: check returns etc.

evalProgram :: Program -> Semantics [[TypeInformation]]
evalProgram (Program functions) = do
	genericListEval evalFunction functions

checkAST :: Program -> ([[TypeInformation]], TypeCheckerState)
checkAST ast =
	Control.Monad.State.runState (evalProgram ast) initialState

interpret :: Program -> ()
interpret _ = ()
