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
type Loc = Int
type Env = Data.Map.Map String Loc
type St  = Data.Map.Map Loc Int

emptyEnv :: Env
emptyEnv = Data.Map.empty

initialSt :: St
initialSt = Data.Map.singleton 0 1 -- na pozycji 0 zapisany jest numer nastepnej wolnej lokacji

type Semantics a = Control.Monad.State.State (Env, St) a
-- albo StateT St (Reader Env) a
-- albo Monada = ReaderT Env (StateT St Identity)

--takeLocation :: Var -> Semantics Loc
--takeLocation var = do
--  Just loc <- asks (M.lookup var)
--  return loc

--takeValue :: Loc -> Semantics Int
--takeValue loc = do
--  Just val <- gets (M.lookup loc)
--  return val
data DeducedType =
	DeducedNone |
	DeducedError |
	DeducedInteger
	deriving (Eq,Ord,Show)


eval :: Expression -> Semantics DeducedType

eval (EAssignment identifier expression) = do
	return DeducedNone

eval (ELess expression1 expression2) = do
	eval expression1

eval (EAdd expression1 expression2) = do
	eval expression1

eval (ECall identifier args) = do
	return DeducedError

eval (EVariable identifier) = do
	return DeducedError

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
	return DeducedNone

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
	evalStatement (statements !! 0)

evalProgram :: Program -> Semantics DeducedType
evalProgram (Program functions) = do
	evalFunction (functions !! 0)

--interpret (SBlock decls stmts) = do
--  env' <- evalDecls decls
--  local (const env') (mapM_ interpret stmts)

--interpret (SAssign var expr) = do
--  val <- eval expr
--  Just loc <-asks (M.lookup var)
--  modify (M.insert loc val)

checkAST :: Program -> (DeducedType, (Env, St))
checkAST ast =
	Control.Monad.State.runState (evalProgram ast) (emptyEnv, initialSt)

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
	case result of
		Bad s -> do
			print "Parse Failed"
			print s
		Ok tree -> do
			print $ checkAST tree
