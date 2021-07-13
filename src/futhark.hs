{-# LANGUAGE OverloadedStrings #-}

-- | The futhark command line tool.
module Main (main) where

import Control.Exception
import Control.Monad
import Data.List (sortOn)
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Futhark.CLI.Autotune as Autotune
import qualified Futhark.CLI.Bench as Bench
import qualified Futhark.CLI.C as C
import qualified Futhark.CLI.CUDA as CCUDA
import qualified Futhark.CLI.Check as Check
import qualified Futhark.CLI.Datacmp as Datacmp
import qualified Futhark.CLI.Dataset as Dataset
import qualified Futhark.CLI.Dev as Dev
import qualified Futhark.CLI.Doc as Doc
import qualified Futhark.CLI.Literate as Literate
import qualified Futhark.CLI.Misc as Misc
import qualified Futhark.CLI.Multicore as Multicore
import qualified Futhark.CLI.MulticoreWASM as MulticoreWASM
import qualified Futhark.CLI.OpenCL as OpenCL
import qualified Futhark.CLI.Pkg as Pkg
import qualified Futhark.CLI.PyOpenCL as PyOpenCL
import qualified Futhark.CLI.Python as Python
import qualified Futhark.CLI.Query as Query
import qualified Futhark.CLI.REPL as REPL
import qualified Futhark.CLI.Run as Run
import qualified Futhark.CLI.Test as Test
import qualified Futhark.CLI.WASM as WASM
import Futhark.Error
import Futhark.Util (maxinum)
import Futhark.Util.Options
import GHC.IO.Encoding (setLocaleEncoding)
import GHC.IO.Exception (IOErrorType (..), IOException (..))
import System.Environment
import System.Exit
import System.IO
import Prelude

type Command = String -> [String] -> IO ()

commands :: [(String, (Command, String))]
commands =
  sortOn
    fst
    [ ("dev", (Dev.main, "Run compiler passes directly.")),
      ("repl", (REPL.main, "Run interactive Read-Eval-Print-Loop.")),
      ("run", (Run.main, "Run a program through the (slow!) interpreter.")),
      ("c", (C.main, "Compile to sequential C.")),
      ("opencl", (OpenCL.main, "Compile to C calling OpenCL.")),
      ("cuda", (CCUDA.main, "Compile to C calling CUDA.")),
      ("multicore", (Multicore.main, "Compile to multicore C.")),
      ("python", (Python.main, "Compile to sequential Python.")),
      ("pyopencl", (PyOpenCL.main, "Compile to Python calling PyOpenCL.")),
      ("wasm", (WASM.main, "Compile to WASM with sequential C")),
      ("wasm-multicore", (MulticoreWASM.main, "Compile to WASM with multicore C")),
      ("test", (Test.main, "Test Futhark programs.")),
      ("bench", (Bench.main, "Benchmark Futhark programs.")),
      ("dataset", (Dataset.main, "Generate random test data.")),
      ("datacmp", (Datacmp.main, "Compare Futhark data files for equality.")),
      ("dataget", (Misc.mainDataget, "Extract test data.")),
      ("doc", (Doc.main, "Generate documentation for Futhark code.")),
      ("pkg", (Pkg.main, "Manage local packages.")),
      ("check", (Check.main, "Type check a program.")),
      ("imports", (Misc.mainImports, "Print all non-builtin imported Futhark files.")),
      ("hash", (Misc.mainHash, "Print hash of program AST.")),
      ("autotune", (Autotune.main, "Autotune threshold parameters.")),
      ("query", (Query.main, "Query semantic information about program.")),
      ("literate", (Literate.main, "Process a literate Futhark program."))
    ]

msg :: String
msg =
  unlines $
    ["<command> options...", "Commands:", ""]
      ++ [ "   " <> cmd <> replicate (k - length cmd) ' ' <> desc
           | (cmd, (_, desc)) <- commands
         ]
  where
    k = maxinum (map (length . fst) commands) + 3

-- | Catch all IO exceptions and print a better error message if they
-- happen.
reportingIOErrors :: IO () -> IO ()
reportingIOErrors =
  flip
    catches
    [ Handler onExit,
      Handler onICE,
      Handler onIOException,
      Handler onError
    ]
  where
    onExit :: ExitCode -> IO ()
    onExit = throwIO

    onICE :: InternalError -> IO ()
    onICE (Error CompilerLimitation s) = do
      T.hPutStrLn stderr "Known compiler limitation encountered.  Sorry."
      T.hPutStrLn stderr "Revise your program or try a different Futhark compiler."
      T.hPutStrLn stderr s
      exitWith $ ExitFailure 1
    onICE (Error CompilerBug s) = do
      T.hPutStrLn stderr "Internal compiler error."
      T.hPutStrLn stderr "Please report this at https://github.com/diku-dk/futhark/issues."
      T.hPutStrLn stderr s
      exitWith $ ExitFailure 1

    onError :: SomeException -> IO ()
    onError e
      | Just UserInterrupt <- asyncExceptionFromException e =
        return () -- This corresponds to CTRL-C, which is not an error.
      | otherwise = do
        T.hPutStrLn stderr "Internal compiler error (unhandled IO exception)."
        T.hPutStrLn stderr "Please report this at https://github.com/diku-dk/futhark/issues"
        T.hPutStrLn stderr $ T.pack $ show e
        exitWith $ ExitFailure 1

    onIOException :: IOException -> IO ()
    onIOException e
      | ioe_type e == ResourceVanished =
        exitWith $ ExitFailure 1
      | otherwise = throw e

main :: IO ()
main = reportingIOErrors $ do
  hSetEncoding stdout utf8
  hSetEncoding stderr utf8
  setLocaleEncoding utf8
  args <- getArgs
  prog <- getProgName
  case args of
    cmd : args'
      | Just (m, _) <- lookup cmd commands -> m (unwords [prog, cmd]) args'
    _ -> mainWithOptions () [] msg (const . const Nothing) prog args
