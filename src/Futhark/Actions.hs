{-# LANGUAGE FlexibleContexts #-}
-- | All (almost) compiler pipelines end with an 'Action', which does
-- something with the result of the pipeline.
module Futhark.Actions
  ( printAction
  , impCodeGenAction
  , kernelImpCodeGenAction
  , metricsAction
  , compileCAction
  , compileOpenCLAction
  , compileCUDAAction
  )
where

import Control.Monad
import Control.Monad.IO.Class
import System.Exit
import System.FilePath
import qualified System.Info

import Futhark.Compiler.CLI
import Futhark.Analysis.Alias
import Futhark.IR
import Futhark.IR.Prop.Aliases
import Futhark.IR.KernelsMem (KernelsMem)
import Futhark.IR.SeqMem (SeqMem)
import qualified Futhark.CodeGen.ImpGen.Sequential as ImpGenSequential
import qualified Futhark.CodeGen.ImpGen.Kernels as ImpGenKernels
import qualified Futhark.CodeGen.Backends.SequentialC as SequentialC
import qualified Futhark.CodeGen.Backends.CCUDA as CCUDA
import qualified Futhark.CodeGen.Backends.COpenCL as COpenCL
import Futhark.Analysis.Metrics
import Futhark.Util (runProgramWithExitCode)

-- | Print the result to stdout, with alias annotations.
printAction :: (ASTLore lore, CanBeAliased (Op lore)) => Action lore
printAction =
  Action { actionName = "Prettyprint"
         , actionDescription = "Prettyprint the resulting internal representation on standard output."
         , actionProcedure = liftIO . putStrLn . pretty . aliasAnalysis
         }

-- | Print metrics about AST node counts to stdout.
metricsAction :: OpMetrics (Op lore) => Action lore
metricsAction =
  Action { actionName = "Compute metrics"
         , actionDescription = "Print metrics on the final AST."
         , actionProcedure = liftIO . putStr . show . progMetrics
         }

-- | Convert the program to sequential ImpCode and print it to stdout.
impCodeGenAction :: Action SeqMem
impCodeGenAction =
  Action { actionName = "Compile imperative"
         , actionDescription = "Translate program into imperative IL and write it on standard output."
         , actionProcedure = liftIO . putStrLn . pretty . snd <=< ImpGenSequential.compileProg
         }

-- | Convert the program to GPU ImpCode and print it to stdout.
kernelImpCodeGenAction :: Action KernelsMem
kernelImpCodeGenAction =
  Action { actionName = "Compile imperative kernels"
         , actionDescription = "Translate program into imperative IL with kernels and write it on standard output."
         , actionProcedure = liftIO . putStrLn . pretty . snd <=< ImpGenKernels.compileProgOpenCL
         }

-- | The @futhark c@ action.
compileCAction :: FutharkConfig -> CompilerMode -> FilePath -> Action SeqMem
compileCAction fcfg mode outpath =
  Action { actionName = "Compile to OpenCL"
         , actionDescription = "Compile to OpenCL"
         , actionProcedure = helper }
  where
    helper prog = do
      cprog <- handleWarnings fcfg $ SequentialC.compileProg prog
      let cpath = outpath `addExtension` "c"
          hpath = outpath `addExtension` "h"

      case mode of
        ToLibrary -> do
          let (header, impl) = SequentialC.asLibrary cprog
          liftIO $ writeFile hpath header
          liftIO $ writeFile cpath impl
        ToExecutable -> do
          liftIO $ writeFile cpath $ SequentialC.asExecutable cprog
          ret <- liftIO $ runProgramWithExitCode "gcc"
                 [cpath, "-O3", "-std=c99", "-lm", "-o", outpath] mempty
          case ret of
            Left err ->
              externalErrorS $ "Failed to run gcc: " ++ show err
            Right (ExitFailure code, _, gccerr) ->
              externalErrorS $ "gcc failed with code " ++
              show code ++ ":\n" ++ gccerr
            Right (ExitSuccess, _, _) ->
              return ()

-- | The @futhark opencl@ action.
compileOpenCLAction :: FutharkConfig -> CompilerMode -> FilePath -> Action KernelsMem
compileOpenCLAction fcfg mode outpath =
  Action { actionName = "Compile to OpenCL"
         , actionDescription = "Compile to OpenCL"
         , actionProcedure = helper }
  where
    helper prog = do
      cprog <- handleWarnings fcfg $ COpenCL.compileProg prog
      let cpath = outpath `addExtension` "c"
          hpath = outpath `addExtension` "h"
          extra_options
            | System.Info.os == "darwin" =
                ["-framework", "OpenCL"]
            | System.Info.os == "mingw32" =
                ["-lOpenCL64"]
            | otherwise =
                ["-lOpenCL"]

      case mode of
        ToLibrary -> do
          let (header, impl) = COpenCL.asLibrary cprog
          liftIO $ writeFile hpath header
          liftIO $ writeFile cpath impl
        ToExecutable -> do
          liftIO $ writeFile cpath $ COpenCL.asExecutable cprog
          ret <- liftIO $ runProgramWithExitCode "gcc"
                 ([cpath, "-O", "-std=c99", "-lm", "-o", outpath] ++ extra_options) mempty
          case ret of
            Left err ->
              externalErrorS $ "Failed to run gcc: " ++ show err
            Right (ExitFailure code, _, gccerr) ->
              externalErrorS $ "gcc failed with code " ++
              show code ++ ":\n" ++ gccerr
            Right (ExitSuccess, _, _) ->
              return ()

-- | The @futhark cuda@ action.
compileCUDAAction :: FutharkConfig -> CompilerMode -> FilePath -> Action KernelsMem
compileCUDAAction fcfg mode outpath =
  Action { actionName = "Compile to CUDA"
         , actionDescription = "Compile to CUDA"
         , actionProcedure = helper }
  where
    helper prog = do
      cprog <- handleWarnings fcfg $ CCUDA.compileProg prog
      let cpath = outpath `addExtension` "c"
          hpath = outpath `addExtension` "h"
          extra_options = [ "-lcuda"
                          , "-lcudart"
                          , "-lnvrtc"
                          ]
      case mode of
        ToLibrary -> do
          let (header, impl) = CCUDA.asLibrary cprog
          liftIO $ writeFile hpath header
          liftIO $ writeFile cpath impl
        ToExecutable -> do
          liftIO $ writeFile cpath $ CCUDA.asExecutable cprog
          let args = [cpath, "-O", "-std=c99", "-lm", "-o", outpath]
                     ++ extra_options
          ret <- liftIO $ runProgramWithExitCode "gcc" args mempty
          case ret of
            Left err ->
              externalErrorS $ "Failed to run gcc: " ++ show err
            Right (ExitFailure code, _, gccerr) ->
              externalErrorS $ "gcc failed with code " ++
              show code ++ ":\n" ++ gccerr
            Right (ExitSuccess, _, _) ->
              return ()
