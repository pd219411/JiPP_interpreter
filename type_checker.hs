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

eval :: Expression -> Semantics Int

eval (EVar var) = do
  Just loc <- asks (M.lookup var)
  Just val <- gets (M.lookup loc)
  return val
eval (EOp op exp1 exp2) = do
  val1 <- eval exp1
  val2 <- eval exp2
  return $ evalOp op val1 val2

eval (EInteger i) = return i

--evalExp :: Exp -> Int
--evalExp expr =
--  let readerStuff = eval expr in
--  let stateStuff = runReaderT readerStuff emptyEnv in
--  evalState stateStuff initialSt

evalDecl :: Decl -> Semantics Env
evalDecl (DVar var expr) = do
  Just newLoc <- gets (M.lookup 0)
  val <- eval expr
  modify (M.insert newLoc val)
  modify (M.insert 0 (newLoc+1))
  env <- ask
  return $ M.insert var newLoc env
-- moĹźna teĹź asks M.insert var newLoc

-- Dodatkowa zabawa, aby druga deklaracja z listy mogla juz uzywac pierwszej zmiennej
evalDecls :: [Decl] -> Semantics Env
evalDecls [] = ask
evalDecls (decl:decls) = do
  env' <- evalDecl decl
  local (const env') (evalDecls decls)

interpret :: Stmt -> Semantics ()
interpret SSkip = return ()

interpret (SBlock decls stmts) = do
  env' <- evalDecls decls
  local (const env') (mapM_ interpret stmts)

interpret (SAssign var expr) = do
  val <- eval expr
  Just loc <-asks (M.lookup var)
  modify (M.insert loc val)

interpret (SIf bexpr stmt1 stmt2) = do
  bval <- eval bexpr
  if bval == 0
     then interpret stmt2
     else interpret stmt1

interpret this@(SWhile bexpr stmt) = do
  bval <- eval bexpr
  if bval == 0
     then return ()
     else do
       interpret stmt
       interpret this

execStmt :: Stmt -> IO ()
execStmt stmt = do
  let ((), finalState) =  runState (runReaderT (interpret stmt) emptyEnv) initialSt
  print finalState
---------------------------------

type ParseFunction a = [Token] -> Err a

run :: (Print a, Show a) => ParseFunction a -> String -> IO ()
run p s =
	let ts = myLexer s in
	case p ts of
		Bad s -> do
			putStrLn "\nParse              Failed...\n"
			--putStrV v "Tokens:"
			--putStrV v $ show ts
			--putStrLn s
		Ok tree -> do
			putStrLn "Parse Successful!"
			--showTree v tree
			putStrLn (show tree)

main = do
	hGetContents stdin >>= run pProgram
