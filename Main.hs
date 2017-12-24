{-# LANGUAGE LambdaCase #-}
module Main (main) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor
import Data.IORef
import Data.List
import qualified Data.Map as Map
import Data.Time
import Data.Version (showVersion)
import System.Directory
import System.FilePath
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline
import System.Exit
import Text.Printf

import Exp.Lex
import Exp.Par
import Exp.Print
import Exp.Abs
import Exp.Layout
import Exp.ErrM


import CTT
import qualified Paths_cubicaltt as CabalFile
import Resolver
import qualified TypeChecker as TC
import qualified Eval as E

type Interpreter a = InputT IO a

-- Flag handling
data Flag = Debug | Batch | Help | Version | Time | Deps
  deriving (Eq,Show)

options :: [OptDescr Flag]
options = [ Option "d"  ["debug"]      (NoArg Debug)   "run in debugging mode"
          , Option "b"  ["batch"]      (NoArg Batch)   "run in batch mode"
          , Option ""   ["help"]       (NoArg Help)    "print help"
          , Option "-t" ["time"]       (NoArg Time)    "measure time spent computing"
          , Option ""   ["version"]    (NoArg Version) "print version number" 
          , Option "g"  ["graph-deps"] (NoArg Deps)    "print dependency graph"
          ]

-- Version number, welcome message, usage and prompt strings
welcome, usage, prompt :: String
version = showVersion CabalFile.version
welcome = "cubical, version: " ++ version ++ "  (:h for help)\n"
usage   = "Usage: cubical [options] <file.ctt>\nOptions:"
prompt  = "> "

lexer :: String -> [Token]
lexer = resolveLayout True . myLexer

showTree :: (Show a, Print a) => a -> IO ()
showTree tree = do
  putStrLn $ "\n[Abstract Syntax]\n\n" ++ show tree
  putStrLn $ "\n[Linearized tree]\n\n" ++ printTree tree

-- Used for auto completion
searchFunc :: [String] -> String -> [Completion]
searchFunc ns str = map simpleCompletion $ filter (str `isPrefixOf`) ns

settings :: IORef [String] -> Settings IO
settings n = Settings
  { historyFile    = Just "cubicaltt.history.txt"
  , complete       = completeWord Nothing " \t" $ ourCompletion n
  , autoAddHistory = True }

compileBatch :: String -> IO ()
compileBatch f = do
  result <- compileFile [] f
  case result of
    Right _ -> exitSuccess
    Left _ -> do
      void $ handleFileErrors result
      exitFailure

ourCompletion :: IORef [String] -> String -> IO [Completion]
ourCompletion n x = do
  ns <- readIORef n
  return $ searchFunc ns x

main :: IO ()
main = do
  completionRef <- newIORef []
  args <- getArgs
  case getOpt Permute options args of
    (flags,files,[])
      | Help    `elem` flags -> putStrLn $ usageInfo usage options
      | Version `elem` flags -> putStrLn version
      | otherwise -> case files of
       []  -> do
         putStrLn welcome
         runInputT (settings completionRef) (loop flags [] Map.empty TC.verboseEnv completionRef)
       [f] -> if Batch `elem` flags
         then compileBatch f
         else do
           putStrLn welcome
           putStrLn $ "Loading " ++ show f
           runInputT (settings completionRef) $ initLoop flags f completionRef
       _   -> putStrLn $ "Input error: zero or one file expected\n\n" ++
                         usageInfo usage options
    (_,_,errs) -> putStrLn $ "Input error: " ++ concat errs ++ "\n" ++
                             usageInfo usage options

shrink :: String -> String
shrink s = s -- if length s > 1000 then take 1000 s ++ "..." else s

wrapResolver deps x = ExceptT $ return $ first OEResolver $ runResolver deps x

wrapExpressionParser exprStr = ExceptT $ return $ first OEParser $ case pExp (lexer exprStr) of
  Bad err -> Left err
  Ok result -> Right result

wrapExpressionTypeChecker tenv body = ExceptT $ first OETypeCheckerExpr <$> TC.runInfer tenv body

wrapTypeChecker :: [Decls] -> Vars -> ExceptT OurError IO TC.TEnv
wrapTypeChecker adefs names = do
  (merr,tenv) <- liftIO $ TC.runDeclss TC.verboseEnv adefs
  ExceptT $ return $ case merr of
    Just err -> Left $ OETypeChecker err names tenv
    Nothing -> Right tenv

compileFile :: [String] -> String -> IO (Either OurError (Bool, Vars, TC.TEnv))
compileFile alreadyCheckedFileNames f = runExceptT $ do
  (_,_,mods) <- imports True ([],alreadyCheckedFileNames,[]) f
  -- Translate to TT
  (adefs, names) <- wrapResolver True $ resolveModules mods
  -- After resolivng the file check if some definitions were shadowed:
  warnDups names
  tenv <- wrapTypeChecker adefs names
  return (null mods, names, tenv)

measureTime flag operation
  | flag = do
    start <- getCurrentTime
    result <- operation
    stop <- getCurrentTime
    -- Compute time and print nicely
    let time = diffUTCTime stop start
        secs = read (takeWhile (/='.') (init (show time)))
        rest = read ('0':dropWhile (/='.') (init (show time)))
        mins = secs `quot` 60
        sec  = printf "%.3f" (fromInteger (secs `rem` 60) + rest :: Float)
    putStrLn $ "Time: " ++ show mins ++ "m" ++ sec ++ "s"
    -- Only print in seconds:
    -- when (Time `elem` flags) $ outputStrLn $ "Time: " ++ show time
    return result
  | otherwise = operation

compileExpr names tenv flags str' = runExceptT $ let
    (msg,str,mod) = case str' of
      (':':'n':' ':str) -> ("NORMEVAL: ",str,E.normal [])
      str -> ("EVAL: ",str,id)
  in do
  exp <- wrapExpressionParser str
  body <- wrapResolver False $ local (insertIdents names) $ resolveExp exp
  _ <-  wrapExpressionTypeChecker tenv body
  liftIO $ measureTime (Time `elem` flags) $ do
    let e = mod $ E.eval (TC.env tenv) body
    -- Let's not crash if the evaluation raises an error:
    putStrLn (msg ++ shrink (show e)) `catch`
                 -- (writeFile "examples/nunivalence3.ctt" (show e))
                 (\e -> putStrLn ("Exception: " ++
                                  show (e :: SomeException)))

data OurError
  = OEResolver String
  | OETypeChecker String Vars TC.TEnv
  | OEImports String
  | OEParser String
  | OETypeCheckerExpr String

handleFileErrors = \case
  Right (noMods, names, tenv) -> do
    unless noMods $ putStrLn "File loaded."
    return (names, tenv)
  Left x -> handleCommonErrors x

handleExprErrors = \case
  Right _ -> return ()
  Left x -> void $ handleCommonErrors x

handleCommonErrors = \case
    OEResolver err -> do
      putStrLn $ "Resolver failed: " ++ err
      return (Map.empty, TC.verboseEnv)
    OETypeChecker err names tenv -> do
      putStrLn $ "Type checking failed: " ++ shrink err
      return (names, tenv)
    OEImports err -> do
      putStrLn err
      return (Map.empty, TC.verboseEnv)
    OETypeCheckerExpr err -> do
      putStrLn $ "Type checking failed: " ++ shrink err
      return (Map.empty, TC.verboseEnv)
    OEParser err -> do
      putStrLn ("Parse error: " ++ err)
      return (Map.empty, TC.verboseEnv)

resumeLoop flags f completionRef (names, tenv) = unless (Batch `elem` flags || Deps `elem` flags) $ do
  -- Compute names for auto completion
  liftIO $ writeIORef completionRef $ Map.keys names
  loop flags f names tenv completionRef

warnDups names = do
  let ns = Map.keys names
      uns = nub ns
      dups = ns \\ uns
  liftIO $ unless (null dups) $
    putStrLn $ "Warning: the following definitions were shadowed [" ++
               intercalate ", " dups ++ "]"

-- Initialize the main loop
initLoop :: [Flag] -> FilePath -> IORef [String] -> Interpreter ()
initLoop flags f completionRef
  = liftIO (compileFile [] f >>= handleFileErrors) >>= resumeLoop flags f completionRef

-- The main loop
loop :: [Flag] -> FilePath -> Vars -> TC.TEnv -> IORef [String] -> Interpreter ()
loop flags f names tenv completionRef = go where
  go :: Interpreter ()
  go = do
    input <- getInputLine prompt
    case input of
      Nothing    -> outputStrLn help >> go
      Just ":q"  -> return ()
      Just ":r"  -> initLoop flags f completionRef
      Just (':':'l':' ':str)
        | ' ' `elem` str -> outputStrLn "Only one file allowed after :l" >> go
        | otherwise      -> initLoop flags str completionRef
      Just x -> go2 x >> go
  go2 :: String -> Interpreter ()
  go2 = liftIO . \case
    (':':'c':'d':' ':str) -> setCurrentDirectory str
    ":h"  -> putStrLn help
    str'  -> compileExpr names tenv flags str' >>= handleExprErrors

-- (not ok,loaded,already loaded defs) -> to load ->
--   (new not ok, new loaded, new defs)
-- the bool determines if it should be verbose or not
imports :: Bool -> ([String],[String],[Module]) -> String ->
           ExceptT OurError IO ([String],[String],[Module])
imports v st@(notok,loaded,mods) f
  | f `elem` notok  = throwError $ OEImports ("Looping imports in " ++ f)
  | f `elem` loaded = return st
  | otherwise       = do
    exists <- liftIO $ doesFileExist f
    unless exists $ throwError $ OEImports (f ++ " does not exist")
    let prefix = dropFileName f
    s <- liftIO $ readFile f
    let ts = lexer s
    case pModule ts of
      Bad s -> throwError $ OEImports ("Parse failed in " ++ show f ++ "\n" ++ show s)
      Ok mod@(Module (AIdent (_,name)) imp decls) -> do
        let imp_ctt = [prefix ++ i ++ ".ctt" | Import (AIdent (_,i)) <- imp]
        when (name /= dropExtension (takeFileName f)) $
          throwError $ OEImports $ "Module name mismatch in " ++ show f ++ " with wrong name " ++ name
        void $ ExceptT $ compileFile (f:loaded) f
        (notok1,loaded1,mods1) <-
          foldM (imports v) (f:notok,loaded,mods) imp_ctt
        liftIO $ when v $ putStrLn $ "Parsed " ++ show f ++ " successfully!"
        return (notok,f:loaded1,mods1 ++ [mod])

help :: String
help = "\nAvailable commands:\n" ++
       "  <statement>     infer type and evaluate statement\n" ++
       "  :n <statement>  normalize statement\n" ++
       "  :q              quit\n" ++
       "  :l <filename>   loads filename (and resets environment before)\n" ++
       "  :cd <path>      change directory to path\n" ++
       "  :r              reload\n" ++
       "  :h              display this message\n"
