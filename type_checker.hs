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
type IdentifierEnvironment = Data.Map.Map Ident Location
type LocationValues = Data.Map.Map Location Type

data TypeCheckerState =
	TypeCheckerState {
		xxx :: IdentifierEnvironment,
		yyy :: LocationValues
	}
	deriving (Eq,Ord,Show)

initialState :: TypeCheckerState
initialState =
	TypeCheckerState { xxx = Data.Map.empty, yyy = Data.Map.empty }

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
	let ret = Data.Map.lookup identifier (xxx state) in
	case ret of
		Nothing -> DeducedError ["Unknown identifier: " ++ string]
		Just v -> getTypeFromLocation (yyy state) v

nextLocation :: IdentifierEnvironment -> Location
nextLocation e =
	if Data.Map.null e
	then 0
	else (maximum (Data.Map.elems e)) + 1

addType :: TypeCheckerState -> Ident -> Type -> TypeCheckerState
addType state identifier type' = --TODO: what if one exists on this level
	let new_location = (nextLocation (xxx state)) in
	TypeCheckerState { xxx = (Data.Map.insert identifier new_location (xxx state)), yyy = (Data.Map.insert new_location type' (yyy state)) }

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

eval (ECall identifier args) = do
	return (DeducedError []) --TODO check if function exists and if params fit args

eval (EVariable identifier) = do
	state <- Control.Monad.State.get
	return (getType state identifier)

eval (EBoolean boolean) = do
	return (DeducedType TBoolean)

eval (EInteger integer) = do
	return (DeducedType TInt)


evalDeclaration :: Declaration -> Semantics TypeInformation
evalDeclaration (Declaration type' identifier) = do
--	Just newLoc <- gets (M.lookup 0)
--	val <- eval expr
--	modify (M.insert newLoc val)
--	modify (M.insert 0 (newLoc+1))
--	env <- ask
--	return $ M.insert var newLoc env
	state <- Control.Monad.State.get
	Control.Monad.State.put (addType state identifier type')
	return DeducedNone

evalDeclarations :: [Declaration] -> Semantics TypeInformation
evalDeclarations [] =
	return DeducedNone
evalDeclarations (x:xs) = do
	tmp <- evalDeclaration x
	evalDeclarations xs
	return tmp

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

evalFunction :: Function -> Semantics TypeInformation
evalFunction (Function type' identifier declarations statements) = do
	tmp <- evalDeclarations declarations
--	TODO: modify environment to include function declaration
	evalStatements statements

evalProgram :: Program -> Semantics TypeInformation
evalProgram (Program functions) = do
	evalFunction (functions !! 0)

--interpret (SBlock decls stmts) = do
--  env' <- evalDecls decls
--  local (const env') (mapM_ interpret stmts)

--interpret (SAssign var expr) = do
--  val <- eval expr
--  Just loc <-asks (M.lookup var)
--  modify (M.insert loc val)

checkAST :: Program -> (TypeInformation, TypeCheckerState)
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
