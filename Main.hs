{-# LANGUAGE LambdaCase #-}
module Main (main) where

import Control.Monad.Except
import Control.Monad.Reader
import Data.Bifunctor
import Data.IORef
import Data.List
import Data.Time
import System.Directory
import System.FilePath
import System.Environment
import System.Console.GetOpt
import System.Console.Haskeline
import Text.Printf

import Exp.Lex
import Exp.Par
import Exp.Print
import Exp.Abs
import Exp.Layout
import Exp.ErrM

import CTT
import Resolver
import qualified TypeChecker as TC
import qualified Eval as E

type Interpreter a = InputT IO a

-- Flag handling
data Flag = Debug | Batch | Help | Version | Time
  deriving (Eq,Show)

options :: [OptDescr Flag]
options = [ Option "d"  ["debug"]   (NoArg Debug)   "run in debugging mode"
          , Option "b"  ["batch"]   (NoArg Batch)   "run in batch mode"
          , Option ""   ["help"]    (NoArg Help)    "print help"
          , Option "-t" ["time"]    (NoArg Time)    "measure time spent computing"
          , Option ""   ["version"] (NoArg Version) "print version number" ]

-- Version number, welcome message, usage and prompt strings
version, welcome, usage, prompt :: String
version = "1.0"
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
         runInputT (settings completionRef) (loop flags [] [] TC.verboseEnv completionRef)
       [f] -> do
         putStrLn welcome
         putStrLn $ "Loading " ++ show f
         runInputT (settings completionRef) $ initLoop flags f completionRef
       _   -> putStrLn $ "Input error: zero or one file expected\n\n" ++
                         usageInfo usage options
    (_,_,errs) -> putStrLn $ "Input error: " ++ concat errs ++ "\n" ++
                             usageInfo usage options

shrink :: String -> String
shrink s = s -- if length s > 1000 then take 1000 s ++ "..." else s

wrapResolver mods = ExceptT $ return $ first OEResolver $ runResolver $ resolveModules mods

wrapTypeChecker :: [Decls] -> [(Ident, SymKind)] -> ExceptT OurError IO TC.TEnv
wrapTypeChecker adefs names = do
  (merr,tenv) <- liftIO $ TC.runDeclss TC.verboseEnv adefs
  ExceptT $ return $ case merr of
    Just err -> Left $ OETypeChecker err names tenv
    Nothing -> Right tenv

compileFile :: String -> IO (Either OurError (Bool, [(Ident, SymKind)], TC.TEnv))
compileFile f = runExceptT $ do
  (_,_,mods) <- imports True ([],[],[]) f
  -- Translate to TT
  (adefs, names) <- wrapResolver mods
  -- After resolivng the file check if some definitions were shadowed:
  warnDups names
  tenv <- wrapTypeChecker adefs names
  return (null mods, names, tenv)

data OurError
  = OEResolver String
  | OETypeChecker String [(CTT.Ident,SymKind)] TC.TEnv
  | OEImports String

handleErrors = \case
  Right (noMods, names, tenv) -> do
    unless noMods $ putStrLn "File loaded."
    return (names, tenv)
  Left x -> case x of
    OEResolver err -> do
      putStrLn $ "Resolver failed: " ++ err
      return ([], TC.verboseEnv)
    OETypeChecker err names tenv -> do
      putStrLn $ "Type checking failed: " ++ shrink err
      return (names, tenv)
    OEImports err -> do
      putStrLn err
      return ([], TC.verboseEnv)

resumeLoop flags f completionRef (names, tenv) = unless (Batch `elem` flags) $ do
  -- Compute names for auto completion
  liftIO $ writeIORef completionRef $ map fst names
  loop flags f names tenv completionRef

warnDups names = do
  let ns = map fst names
      uns = nub ns
      dups = ns \\ uns
  liftIO $ unless (null dups) $
    putStrLn $ "Warning: the following definitions were shadowed [" ++
               intercalate ", " dups ++ "]"

-- Initialize the main loop
initLoop :: [Flag] -> FilePath -> IORef [String] -> Interpreter ()
initLoop flags f completionRef
  = liftIO (compileFile f >>= handleErrors) >>= resumeLoop flags f completionRef

-- The main loop
loop :: [Flag] -> FilePath -> [(CTT.Ident,SymKind)] -> TC.TEnv -> IORef [String] -> Interpreter ()
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
  go2 = \case
    (':':'c':'d':' ':str) -> liftIO (setCurrentDirectory str)
    ":h"  -> outputStrLn help
    str'  ->
      let (msg,str,mod) = case str' of
            (':':'n':' ':str) ->
              ("NORMEVAL: ",str,E.normal [])
            str -> ("EVAL: ",str,id)
      in case pExp (lexer str) of
      Bad err -> outputStrLn ("Parse error: " ++ err)
      Ok  exp ->
        case runResolver $ local (insertIdents names) $ resolveExp exp of
          Left  err  -> outputStrLn ("Resolver failed: " ++ err)
          Right body -> do
            x <- liftIO $ TC.runInfer tenv body
            case x of
              Left err -> outputStrLn ("Could not type-check: " ++ err)
              Right _  -> do
                start <- liftIO getCurrentTime
                let e = mod $ E.eval (TC.env tenv) body
                -- Let's not crash if the evaluation raises an error:
                liftIO $ catch (putStrLn (msg ++ shrink (show e)))
                               -- (writeFile "examples/nunivalence3.ctt" (show e))
                               (\e -> putStrLn ("Exception: " ++
                                                show (e :: SomeException)))
                stop <- liftIO getCurrentTime
                -- Compute time and print nicely
                let time = diffUTCTime stop start
                    secs = read (takeWhile (/='.') (init (show time)))
                    rest = read ('0':dropWhile (/='.') (init (show time)))
                    mins = secs `quot` 60
                    sec  = printf "%.3f" (fromInteger (secs `rem` 60) + rest :: Float)
                when (Time `elem` flags) $
                   outputStrLn $ "Time: " ++ show mins ++ "m" ++ sec ++ "s"
                -- Only print in seconds:
                -- when (Time `elem` flags) $ outputStrLn $ "Time: " ++ show time

-- (not ok,loaded,already loaded defs) -> to load ->
--   (new not ok, new loaded, new defs)
-- the bool determines if it should be verbose or not
imports :: Bool -> ([String],[String],[Module]) -> String ->
           ExceptT OurError IO ([String],[String],[Module])
imports v st@(notok,loaded,mods) f
  | f `elem` notok  = throwError $ OEImports ("Looping imports in " ++ f)
  | f `elem` loaded = return st
  | otherwise       = do
    b <- liftIO $ doesFileExist f
    when (not b) $ throwError $ OEImports (f ++ " does not exist")
    let prefix = dropFileName f
    s <- liftIO $ readFile f
    let ts = lexer s
    case pModule ts of
      Bad s -> throwError $ OEImports ("Parse failed in " ++ show f ++ "\n" ++ show s)
      Ok mod@(Module (AIdent (_,name)) imp decls) -> do
        let imp_ctt = [prefix ++ i ++ ".ctt" | Import (AIdent (_,i)) <- imp]
        when (name /= dropExtension (takeFileName f)) $
          throwError $ OEImports $ "Module name mismatch in " ++ show f ++ " with wrong name " ++ name
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
