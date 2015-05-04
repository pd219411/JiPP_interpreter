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
typeIsOfType info type'=
	case info of
		DeducedType type' -> True
		_ -> False

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

typeOperationSame :: TypeInformation -> TypeInformation -> TypeInformation
typeOperationSame type1 type2 =
	if type1 == type2
	then type1
	else DeducedError

typeAssignment :: TypeInformation -> TypeInformation -> TypeInformation
typeAssignment type1 type2 =
	if type1 == type2
	then DeducedNone
	else DeducedError

typeOperationToBoolean :: TypeInformation -> TypeInformation -> TypeInformation
typeOperationToBoolean type1 type2 =
	if type1 == type2
	then DeducedType TBoolean
	else DeducedError --["type combo error less " ++ (show type1)]

typeStatement :: TypeInformation -> TypeInformation -> TypeInformation
typeStatement DeducedNone type' = type'
typeStatement type' DeducedNone = type'
--typeStatement (DeducedError m1) (DeducedError m2) = DeducedError (m1 ++ m2)
typeStatement DeducedError DeducedError = DeducedError
--typeStatement type1 type2  = (DeducedError ["TODO deduction"])
typeStatement type1 type2  = DeducedError --["TODO deduction"])

errorFold :: [TypeInformation] -> String -> TypeInformation
errorFold infos error_message =
	if (any typeIsError infos)
	then DeducedError --[error_message])
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
	expressionCheck (typeOperationSame type1 type2) (generateError node "type mismatch")

evalExpression node@(ELess expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationToBoolean type1 type2) (generateError node "type mismatch")

evalExpression node@(EAdd expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationSame type1 type2) (generateError node "type mismatch")

evalExpression node@(ESub expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	expressionCheck (typeOperationSame type1 type2) (generateError node "type mismatch")

evalExpression node@(EMul expression1 expression2) = do
	type1 <- evalExpression expression1
	type2 <- evalExpression expression2
	return (typeOperationSame type1 type2)

evalExpression node@(ECall identifier args) = do
	state <- Control.Monad.State.get
	case (getFunction state identifier) of
		Nothing -> do
			reportError (generateError node "unknown function identifier")
			return DeducedError
		Just info -> do
			types <- (genericListEval evalExpression args)
			reportErrorIf (not (argsListOK (snd info) types)) (generateError node "bad of arguments")
			return (DeducedType (fst info))

evalExpression node@(EVariable identifier@(Ident string)) = do
	state <- Control.Monad.State.get
	case (allVariable state identifier) of
		Nothing -> do
			reportError (generateError node "unknown identifier")
			return DeducedError
		Just type' -> return (DeducedType type')

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
			return DeducedNone
		Just _ -> do
			reportError (generateError node "redefinition of variable")
			return DeducedError

evalArgumentDeclaration :: ArgumentDeclaration -> Semantics TypeInformation
evalArgumentDeclaration node@(ArgumentDeclaration type' identifier) =
	declareHelper node type' identifier

evalVariableDeclaration :: VariableDeclaration -> Semantics TypeInformation
evalVariableDeclaration node@(VariableDeclaration type' identifier) =
	declareHelper node type' identifier

evalStatement :: Statement -> Semantics TypeInformation

evalStatement node@(SAssignment identifier@(Ident string) expression) = do
	state <- Control.Monad.State.get
	case (allVariable state identifier) of
		Nothing -> do
			reportError (generateError node "unknown identifier")
			return DeducedError
		Just variable_type -> do
			expression_info <- evalExpression expression
			let deduced = typeAssignment (DeducedType variable_type) expression_info
			reportErrorIf (typeIsError deduced) "Type mismatch in assignment"
			return deduced

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
	else return DeducedError --["Condition not a boolean"])

evalStatement (SIfElse expression statements1 statements2) = do
	expression_info <- evalExpression expression
	--TODO: open block
	info1 <- evalStatements statements1
	info2 <- evalStatements statements2
	if (typeIsOfType expression_info TBoolean)
	--then return (errorFold [statements_info] "if contains an error")
	then return (typeOperationSame info1 info2)
	else return DeducedError --["Condition not a boolean"])

evalStatement (SWhile expression statements) =
	evalStatement (SIfBare expression statements)

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
		DeducedType _ -> return DeducedError --["Ureachable code"])
		_ -> return info

typeFromDeclaration :: ArgumentDeclaration -> Type
typeFromDeclaration (ArgumentDeclaration type' identifier) = type'

evalFunction :: Function -> Semantics TypeInformation
evalFunction (Function type' identifier@(Ident string) declarations statements) = do
	state_on_enter <- Control.Monad.State.get
	case (getFunction state_on_enter identifier) of
		Just _ -> return DeducedError --["Redefinition of function: " ++ string])
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
		False -> return DeducedError --["main() does not exist"])
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
			--print compile_info
			print "============================= ending state:"
			if (null (errors state))
			then do
				--TODO: remove double checking
				if compile_info == DeducedNone
				then do
					print "=============== LETS DO THIS:"
					print (interpret tree)
					System.Exit.exitWith (System.Exit.ExitSuccess)
				else do
					print "Fail"
			else do
				print (errors state)
				System.Exit.exitWith (System.Exit.ExitFailure 1)
