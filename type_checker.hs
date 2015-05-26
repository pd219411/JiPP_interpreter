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
import qualified System.Exit

--------------------------------
data TypeInformation =
	DeducedNone |
	DeducedError |
	DeducedType Type
	deriving (Eq,Ord,Show)

typeIsError :: TypeInformation -> Bool
typeIsError info =
	case info of
		DeducedError -> True
		_ -> False

typeIsOfType :: TypeInformation -> Type -> Bool
typeIsOfType info type' =
	info == (DeducedType type')

type Location = Int
type FunctionTypeInformation = (Type, [Type])
type FunctionsEnvironment = Data.Map.Map Ident FunctionTypeInformation
type VariablesEnvironment = [Data.Map.Map Ident Location]
type LocationValues = Data.Map.Map Location Type
type Error = String


data TypeCheckerState =
	TypeCheckerState {
		functions :: FunctionsEnvironment,
		variables :: VariablesEnvironment,
		locations :: LocationValues,
		errors :: [Error]
	}
	deriving (Eq,Ord,Show)

initialState :: TypeCheckerState
initialState =
	TypeCheckerState {
		functions = Data.Map.empty,
		variables = [],
		locations = Data.Map.empty,
		errors = []
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
		locations = (locations state),
		errors = (errors state)
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
		locations = (locations state),
		errors = (errors state)
	}

leaveBlock :: TypeCheckerState -> TypeCheckerState
leaveBlock state =
	TypeCheckerState {
		functions = (functions state),
		variables = tail (variables state),
		locations = (locations state),
		errors = (errors state)
	}

addVariable :: TypeCheckerState -> Ident -> Type -> TypeCheckerState
addVariable state identifier type' =
	let new_location = (nextLocation (locations state)) in
	TypeCheckerState {
		functions = (functions state),
		variables = (addToVariablesEnvironment (variables state) identifier new_location),
		locations = (Data.Map.insert new_location type' (locations state)),
		errors = (errors state)
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

addError :: TypeCheckerState -> Error -> TypeCheckerState
addError state error =
	TypeCheckerState {
		functions = (functions state),
		variables = (variables state),
		locations = (locations state),
		errors = (errors state) ++ [error]
	}


reportError :: Error -> Semantics ()
reportError error = do
	Control.Monad.State.modify (\state -> addError state error)

reportErrorIf :: Bool -> Error -> Semantics ()
reportErrorIf condition error = do
	if condition
	then reportError error
	else return ()


typeOperationGeneric :: TypeInformation -> TypeInformation -> Type -> Type -> TypeInformation
typeOperationGeneric type1 type2 expected returned =
	if type1 == type2
	then
		if typeIsOfType type1 expected
		then DeducedType returned
		else DeducedError
	else DeducedError

typeOperationGeneric1 :: TypeInformation -> Type -> TypeInformation
typeOperationGeneric1 type' expected =
	if typeIsOfType type' expected
	then type'
	else DeducedError

typeAssignment :: TypeInformation -> TypeInformation -> TypeInformation
typeAssignment type1 type2 =
	if type1 == type2
	then DeducedNone
	else DeducedError

typeStatementIf :: TypeInformation -> TypeInformation -> TypeInformation
typeStatementIf type1 type2 =
	if type1 == type2
	then type1
	else DeducedNone

genericListEval :: (a -> Semantics e) -> [a] -> Semantics [e]
genericListEval evaluator abstraction_list =
		case abstraction_list of
		[] -> return []
		(abstraction:xs) -> do
			head <- (evaluator abstraction)
			tail <- (genericListEval evaluator xs)
			return (head:tail)

generateError :: Print a => a -> String -> Error
generateError node description =
	description ++ " in " ++ (printTree node)

---------------------------------------------------------

expressionCheck :: TypeInformation -> Error -> Semantics TypeInformation
expressionCheck type_info error = do
	reportErrorIf (typeIsError type_info) error
	return type_info

evalExpression :: Expression -> Semantics TypeInformation

evalExpression node@(EEqual expression1 expression2) = do
	--TODO: copy paste from less; but this should also work for user defined types
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TInt TBoolean) (generateError node "type mismatch")

evalExpression node@(ELess expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TInt TBoolean) (generateError node "type mismatch")

evalExpression node@(ELessEqual expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TInt TBoolean) (generateError node "type mismatch")

evalExpression node@(EAdd expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TInt TInt) (generateError node "type mismatch")

evalExpression node@(ESub expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TInt TInt) (generateError node "type mismatch")

evalExpression node@(EMul expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TInt TInt) (generateError node "type mismatch")

evalExpression node@(EDiv expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TInt TInt) (generateError node "type mismatch")

evalExpression node@(EMod expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TInt TInt) (generateError node "type mismatch")

evalExpression node@(EAnd expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TBoolean TBoolean) (generateError node "type mismatch")

evalExpression node@(EOr expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationGeneric type1 type2 TBoolean TBoolean) (generateError node "type mismatch")

evalExpression node@(ENot expression1) = do
	type1 <- evalExpression expression1
	expressionCheck (typeOperationGeneric1 type1 TBoolean) (generateError node "type mismatch")

evalExpression node@(ECall identifier args) = do
	state <- Control.Monad.State.get
	case (getFunction state identifier) of
		Nothing -> do
			type1 <- evalExpression (EVariable identifier)
			case type1 of
				DeducedType (TFunction return_type param_types) -> do
					types <- (genericListEval evalExpression args)
					reportErrorIf (not (argsListOK param_types types)) (generateError node "bad arguments")
					return (DeducedType return_type)
				_ -> do
					reportError (generateError node "unknown function identifier")
					return DeducedError
		Just info -> do
			types <- (genericListEval evalExpression args)
			reportErrorIf (not (argsListOK (snd info) types)) (generateError node "bad arguments")
			return (DeducedType (fst info))

evalExpression node@(EReference lvalue) = do
	--state <- Control.Monad.State.get
	--type1 <- evalLvalue lvalue
	lvalue_info <- evalLvalue lvalue
	case lvalue_info of
		(DeducedType type') -> do
			return (DeducedType (TPointer type'))
		_ -> do
			reportError (generateError node "bad location")
			return DeducedNone

evalExpression node@(ELvalue lvalue) = do
	evalLvalue lvalue

evalExpression node@(ENewArray type' size initial_value_expression) = do
	type1 <- evalExpression size
	type2 <- evalExpression initial_value_expression
	reportErrorIf (not (typeIsOfType type1 TInt)) (generateError node "size is not an integer")
	reportErrorIf (not ((DeducedType type') == type2)) (generateError node "initial value type mismatch")
	return (DeducedType (TPointer type'))

evalExpression node@(EVariable identifier@(Ident string)) = do
	state <- Control.Monad.State.get
	case (getFunction state identifier) of
		Nothing -> do
			case (allVariable state identifier) of
				Nothing -> do
					reportError (generateError node "unknown identifier")
					return DeducedError
				Just type' -> return (DeducedType type')
		Just (return_type, param_types) -> do
			return (DeducedType (TFunction return_type param_types))


evalExpression (EBoolean boolean) = do
	return (DeducedType TBoolean)

evalExpression (EInteger integer) = do
	return (DeducedType TInt)

argsListOK :: [Type] -> [TypeInformation] -> Bool
argsListOK l1 l2 =
	(map (\type' -> (DeducedType type')) l1) == l2


declareHelper :: Print a => a -> Type -> Ident -> Semantics TypeInformation
declareHelper node type' identifier@(Ident string) = do
	state <- Control.Monad.State.get
	case (topVariable state identifier) of
		Nothing -> do
			Control.Monad.State.modify (\state -> addVariable state identifier type')
		Just _ -> do
			reportError (generateError node "redefinition of variable")
	return DeducedNone

evalArgumentDeclaration :: ArgumentDeclaration -> Semantics TypeInformation
evalArgumentDeclaration node@(ArgumentDeclaration type' identifier) =
	declareHelper node type' identifier

evalVariableDeclaration :: VariableDeclaration -> Semantics TypeInformation
evalVariableDeclaration node@(VariableDeclaration type' identifier) =
	declareHelper node type' identifier


evalLvalue :: Lvalue -> Semantics TypeInformation

evalLvalue node@(LIdentifier identifier) = do
	state <- Control.Monad.State.get
	case (allVariable state identifier) of
		Nothing -> do
			reportError (generateError node "unknown identifier")
			return DeducedNone
		Just variable_type -> do
			return (DeducedType variable_type)

evalLvalue node@(LAddress lvalue) = do
	lvalue_info <- evalLvalue lvalue
	case lvalue_info of
		(DeducedType (TPointer type')) -> do
			return (DeducedType type')
		_ -> do
			reportError (generateError node "not a pointer")
			return DeducedNone

evalLvalue node@(LIndex identifier expression) = do
	type1 <- evalExpression expression
	reportErrorIf (not (typeIsOfType type1 TInt)) (generateError node "index is not an integer")
	evalLvalue (LAddress (LIdentifier identifier))

evalStatement :: Statement -> Semantics TypeInformation

evalStatement node@(SAssignment lvalue expression) = do
	lvalue_info <- evalLvalue lvalue
	expression_info <- evalExpression expression
	let deduced = typeAssignment lvalue_info expression_info
	reportErrorIf (typeIsError deduced) (generateError node "type mismatch")
	return DeducedNone

evalStatement (SBlock statements) = do
	Control.Monad.State.modify openBlock
	temp <- evalStatements statements
	Control.Monad.State.modify leaveBlock
	return temp

evalStatement (SDeclaration declaration@(VariableDeclaration type' identifier) expression) = do
	_ <- evalVariableDeclaration declaration
	evalStatement (SAssignment (LIdentifier identifier) expression)

evalStatement (SExpression expression) = do
	_ <- evalExpression expression
	return DeducedNone

evalStatement node@(SIfBare expression statements) = do
	evalStatement (SIfElse expression statements [])

evalStatement node@(SIfElse expression statements1 statements2) = do
	expression_info <- evalExpression expression
	reportErrorIf (not (typeIsOfType expression_info TBoolean)) (generateError expression "condition not a boolean")
	info1 <- evalStatement (SBlock statements1)
	info2 <- evalStatement (SBlock statements2)
	return (typeStatementIf info1 info2)

evalStatement (SWhile expression statements) =
	evalStatement (SIfBare expression statements)

evalStatement (SPrint print) = do
	evalPrint print

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
		DeducedType _ -> do
			reportError (generateError xs "ureachable code")
			return info
		_ -> return info

evalPrint ::PrintStatement -> Semantics TypeInformation
evalPrint (PrintString _) = do
	return DeducedNone
evalPrint node@(PrintInteger expression) = do
	expression_info <- evalExpression expression
	let deduced = typeAssignment (DeducedType TInt) expression_info
	reportErrorIf (typeIsError deduced) (generateError node "expression not an integer")
	return DeducedNone

typeFromDeclaration :: ArgumentDeclaration -> Type
typeFromDeclaration (ArgumentDeclaration type' identifier) = type'

evalFunction :: Function -> Semantics TypeInformation
evalFunction (Function type' identifier@(Ident string) declarations statements) = do
	state_on_enter <- Control.Monad.State.get
	case (getFunction state_on_enter identifier) of
		Just _ -> do
			reportError (generateError identifier "function redefinition")
			return DeducedError
		Nothing -> do
			Control.Monad.State.modify (\state -> addFunction state identifier (type', map typeFromDeclaration declarations))
			Control.Monad.State.modify openBlock
			temp1 <- genericListEval evalArgumentDeclaration declarations
			temp2 <- evalStatements statements
			Control.Monad.State.modify leaveBlock
			reportErrorIf (temp2 == DeducedNone) (generateError identifier "no return")
			reportErrorIf (temp2 /= DeducedNone && temp2 /= (DeducedType type')) (generateError identifier "return type mismatch")
			return DeducedNone

isMain :: Function -> Bool
isMain (Function _ (Ident string) declarations statements) =
	string == "main" && declarations == []

evalProgram :: Program -> Semantics [TypeInformation]
evalProgram (Program functions) = do
	reportErrorIf (not (any isMain functions)) ("program missing main() function")
	genericListEval evalFunction functions

checkAST :: Program -> ([TypeInformation], TypeCheckerState)
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
	--print result
	case result of
		Bad s -> do
			print "Parse Failed"
			print s
			System.Exit.exitWith (System.Exit.ExitFailure 1)
		Ok tree -> do
			let (compile_info, state) = (checkAST tree)
			--print compile_info
			if (null (errors state))
			then do
				(main_return, interpreter_internals) <- (interpret tree)
				--print main_return
				System.Exit.exitWith (System.Exit.ExitSuccess)
			else do
				print (errors state)
				System.Exit.exitWith (System.Exit.ExitFailure 1)
