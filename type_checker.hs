import System.IO ( stdin, hGetContents )

import LexCredo
import ParCredo
import SkelCredo
import PrintCredo
import AbsCredo

import ErrM


import qualified Data.Map
--import Control.Monad.Reader
import qualified Control.Monad.State
--------------------------------
data DeducedType =
	DeducedNone |
	DeducedError [String] |
	DeducedInteger
	deriving (Eq,Ord,Show)

deduceFromType :: Type -> DeducedType
deduceFromType type' =
	case type' of
		TBoolean -> DeducedError ["TODO: support booleans"]
		TInt -> DeducedInteger

type Location = Int
type IdentifierEnvironment = Data.Map.Map Ident Location
type LocationValues = Data.Map.Map Location DeducedType

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

getTypeFromLocation :: LocationValues -> Location -> DeducedType
getTypeFromLocation m l =
	let ret = Data.Map.lookup l m in
	case ret of
		Nothing -> DeducedError ["Unknown location"]
		Just v -> v

getType :: TypeCheckerState -> Ident -> DeducedType
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

addType :: TypeCheckerState -> Ident -> DeducedType -> TypeCheckerState
addType state identifier type' = --TODO: what if one exists on this level
	let new_location = (nextLocation (xxx state)) in
	TypeCheckerState { xxx = (Data.Map.insert identifier new_location (xxx state)), yyy = (Data.Map.insert new_location type' (yyy state)) }


eval :: Expression -> Semantics DeducedType

eval (EAssignment identifier expression) = do
	return DeducedNone

eval (ELess expression1 expression2) = do
	eval expression1

eval (EAdd expression1 expression2) = do
	eval expression1

eval (ECall identifier args) = do
	return (DeducedError [])

eval (EVariable identifier) = do
	state <- Control.Monad.State.get
	return (getType state identifier)

--eval (EBoolean boolean) = do
--	return DeducedBoolean

eval (EInteger integer) = do
	return DeducedInteger

--eval (EVar var) = do
--  Just loc <- asks (M.lookup var)
--  Just val <- gets (M.lookup loc)
--  return val

--evalExp :: Exp -> Int
--evalExp expr =
--  let readerStuff = eval expr in
--  let stateStuff = runReaderT readerStuff emptyEnv in
--  evalState stateStuff initialSt

evalDeclaration :: Declaration -> Semantics DeducedType
evalDeclaration (Declaration type' identifier) = do
--	Just newLoc <- gets (M.lookup 0)
--	val <- eval expr
--	modify (M.insert newLoc val)
--	modify (M.insert 0 (newLoc+1))
--	env <- ask
--	return $ M.insert var newLoc env
	state <- Control.Monad.State.get
	Control.Monad.State.put (addType state identifier (deduceFromType type'))
	return DeducedNone

evalDeclarations :: [Declaration] -> Semantics DeducedType
evalDeclarations [] =
	return DeducedNone
evalDeclarations (x:xs) = do
	tmp <- evalDeclaration x
	evalDeclarations xs
	return tmp

-- Dodatkowa zabawa, aby druga deklaracja z listy mogla juz uzywac pierwszej zmiennej
--evalDecls :: [Decl] -> Semantics Env
--evalDecls [] = ask
--evalDecls (decl:decls) = do
--  env' <- evalDecl decl
--  local (const env') (evalDecls decls)

evalStatement :: Statement -> Semantics DeducedType
evalStatement (SDeclaration declaration) = do
	evalDeclaration declaration

evalStatement (SExpression expression) = do
	eval expression

evalStatement (SBlock statements) = do
	evalStatement (statements !! 0)

evalFunction :: Function -> Semantics DeducedType
evalFunction (Function type' identifier declarations statements) = do
	--new_state <- evalDeclaration (declarations !! 0)
	tmp <- evalDeclarations declarations
	--Control.Monad.State.put new_state
	--Control.Monad.State.modify (\x -> (addType x (Ident "ZLO") (DeducedError ["TEST KWAS"])))
	case statements of
		[] -> return DeducedNone
		(x:xs) -> evalStatement x
	--evalStatement x

evalProgram :: Program -> Semantics DeducedType
evalProgram (Program functions) = do
	evalFunction (functions !! 0)
	return DeducedNone

--interpret (SBlock decls stmts) = do
--  env' <- evalDecls decls
--  local (const env') (mapM_ interpret stmts)

--interpret (SAssign var expr) = do
--  val <- eval expr
--  Just loc <-asks (M.lookup var)
--  modify (M.insert loc val)

checkAST :: Program -> (DeducedType, TypeCheckerState)
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
