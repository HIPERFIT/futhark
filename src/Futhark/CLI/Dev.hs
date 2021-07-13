{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}

-- | Futhark Compiler Driver
module Futhark.CLI.Dev (main) where

import Control.Category (id)
import Control.Monad
import Control.Monad.State
import Data.List (intersperse)
import Data.Maybe
import qualified Data.Text as T
import qualified Data.Text.IO as T
import Futhark.Actions
import qualified Futhark.Analysis.Alias as Alias
import Futhark.Analysis.Metrics (OpMetrics)
import Futhark.Compiler.CLI hiding (compilerMain)
import Futhark.IR (ASTRep, Op, Prog, pretty)
import qualified Futhark.IR.GPU as GPU
import qualified Futhark.IR.GPUMem as GPUMem
import qualified Futhark.IR.MC as MC
import qualified Futhark.IR.MCMem as MCMem
import Futhark.IR.Parse
import Futhark.IR.Prop.Aliases (CanBeAliased)
import qualified Futhark.IR.SOACS as SOACS
import qualified Futhark.IR.Seq as Seq
import qualified Futhark.IR.SeqMem as SeqMem
import Futhark.Internalise.Defunctionalise as Defunctionalise
import Futhark.Internalise.Defunctorise as Defunctorise
import Futhark.Internalise.LiftLambdas as LiftLambdas
import Futhark.Internalise.Monomorphise as Monomorphise
import Futhark.Optimise.CSE
import Futhark.Optimise.DoubleBuffer
import Futhark.Optimise.Fusion
import Futhark.Optimise.InPlaceLowering
import Futhark.Optimise.InliningDeadFun
import qualified Futhark.Optimise.ReuseAllocations as ReuseAllocations
import Futhark.Optimise.Sink
import Futhark.Optimise.TileLoops
import Futhark.Optimise.Unstream
import Futhark.Pass
import Futhark.Pass.ExpandAllocations
import qualified Futhark.Pass.ExplicitAllocations.GPU as GPU
import qualified Futhark.Pass.ExplicitAllocations.Seq as Seq
import Futhark.Pass.ExtractKernels
import Futhark.Pass.ExtractMulticore
import Futhark.Pass.FirstOrderTransform
import Futhark.Pass.KernelBabysitting
import Futhark.Pass.Simplify
import Futhark.Passes
import Futhark.TypeCheck (Checkable, checkProg)
import Futhark.Util.Log
import Futhark.Util.Options
import qualified Futhark.Util.Pretty as PP
import Language.Futhark.Core (nameFromString)
import Language.Futhark.Parser (parseFuthark)
import System.Exit
import System.FilePath
import System.IO
import Prelude hiding (id)

-- | What to do with the program after it has been read.
data FutharkPipeline
  = -- | Just print it.
    PrettyPrint
  | -- | Run the type checker; print type errors.
    TypeCheck
  | -- | Run this pipeline.
    Pipeline [UntypedPass]
  | -- | Partially evaluate away the module language.
    Defunctorise
  | -- | Defunctorise and monomorphise.
    Monomorphise
  | -- | Defunctorise, monomorphise, and lambda-lift.
    LiftLambdas
  | -- | Defunctorise, monomorphise, lambda-lift, and defunctionalise.
    Defunctionalise

data Config = Config
  { futharkConfig :: FutharkConfig,
    -- | Nothing is distinct from a empty pipeline -
    -- it means we don't even run the internaliser.
    futharkPipeline :: FutharkPipeline,
    futharkCompilerMode :: CompilerMode,
    futharkAction :: UntypedAction,
    -- | If true, prints programs as raw ASTs instead
    -- of their prettyprinted form.
    futharkPrintAST :: Bool
  }

-- | Get a Futhark pipeline from the configuration - an empty one if
-- none exists.
getFutharkPipeline :: Config -> [UntypedPass]
getFutharkPipeline = toPipeline . futharkPipeline
  where
    toPipeline (Pipeline p) = p
    toPipeline _ = []

data UntypedPassState
  = SOACS (Prog SOACS.SOACS)
  | GPU (Prog GPU.GPU)
  | MC (Prog MC.MC)
  | Seq (Prog Seq.Seq)
  | GPUMem (Prog GPUMem.GPUMem)
  | MCMem (Prog MCMem.MCMem)
  | SeqMem (Prog SeqMem.SeqMem)

getSOACSProg :: UntypedPassState -> Maybe (Prog SOACS.SOACS)
getSOACSProg (SOACS prog) = Just prog
getSOACSProg _ = Nothing

class Representation s where
  -- | A human-readable description of the representation expected or
  -- contained, usable for error messages.
  representation :: s -> String

instance Representation UntypedPassState where
  representation (SOACS _) = "SOACS"
  representation (GPU _) = "GPU"
  representation (MC _) = "MC"
  representation (Seq _) = "Seq"
  representation (GPUMem _) = "GPUMem"
  representation (MCMem _) = "MCMem"
  representation (SeqMem _) = "SeqMEm"

instance PP.Pretty UntypedPassState where
  ppr (SOACS prog) = PP.ppr prog
  ppr (GPU prog) = PP.ppr prog
  ppr (MC prog) = PP.ppr prog
  ppr (Seq prog) = PP.ppr prog
  ppr (SeqMem prog) = PP.ppr prog
  ppr (MCMem prog) = PP.ppr prog
  ppr (GPUMem prog) = PP.ppr prog

newtype UntypedPass
  = UntypedPass
      ( UntypedPassState ->
        PipelineConfig ->
        FutharkM UntypedPassState
      )

type BackendAction rep = FutharkConfig -> CompilerMode -> FilePath -> Action rep

data UntypedAction
  = SOACSAction (Action SOACS.SOACS)
  | GPUAction (Action GPU.GPU)
  | GPUMemAction (BackendAction GPUMem.GPUMem)
  | MCMemAction (BackendAction MCMem.MCMem)
  | SeqMemAction (BackendAction SeqMem.SeqMem)
  | PolyAction
      ( forall rep.
        ( ASTRep rep,
          (CanBeAliased (Op rep)),
          (OpMetrics (Op rep))
        ) =>
        Action rep
      )

instance Representation UntypedAction where
  representation (SOACSAction _) = "SOACS"
  representation (GPUAction _) = "GPU"
  representation (GPUMemAction _) = "GPUMem"
  representation (MCMemAction _) = "MCMem"
  representation (SeqMemAction _) = "SeqMem"
  representation PolyAction {} = "<any>"

newConfig :: Config
newConfig = Config newFutharkConfig (Pipeline []) ToExecutable action False
  where
    action = PolyAction printAction

changeFutharkConfig ::
  (FutharkConfig -> FutharkConfig) ->
  Config ->
  Config
changeFutharkConfig f cfg = cfg {futharkConfig = f $ futharkConfig cfg}

type FutharkOption = FunOptDescr Config

passOption :: String -> UntypedPass -> String -> [String] -> FutharkOption
passOption desc pass short long =
  Option
    short
    long
    ( NoArg $
        Right $ \cfg ->
          cfg {futharkPipeline = Pipeline $ getFutharkPipeline cfg ++ [pass]}
    )
    desc

kernelsMemProg ::
  String ->
  UntypedPassState ->
  FutharkM (Prog GPUMem.GPUMem)
kernelsMemProg _ (GPUMem prog) =
  return prog
kernelsMemProg name rep =
  externalErrorS $
    "Pass " ++ name
      ++ " expects GPUMem representation, but got "
      ++ representation rep

soacsProg :: String -> UntypedPassState -> FutharkM (Prog SOACS.SOACS)
soacsProg _ (SOACS prog) =
  return prog
soacsProg name rep =
  externalErrorS $
    "Pass " ++ name
      ++ " expects SOACS representation, but got "
      ++ representation rep

kernelsProg :: String -> UntypedPassState -> FutharkM (Prog GPU.GPU)
kernelsProg _ (GPU prog) =
  return prog
kernelsProg name rep =
  externalErrorS $
    "Pass " ++ name ++ " expects GPU representation, but got " ++ representation rep

typedPassOption ::
  Checkable torep =>
  (String -> UntypedPassState -> FutharkM (Prog fromrep)) ->
  (Prog torep -> UntypedPassState) ->
  Pass fromrep torep ->
  String ->
  FutharkOption
typedPassOption getProg putProg pass short =
  passOption (passDescription pass) (UntypedPass perform) short long
  where
    perform s config = do
      prog <- getProg (passName pass) s
      putProg <$> runPipeline (onePass pass) config prog

    long = [passLongOption pass]

soacsPassOption :: Pass SOACS.SOACS SOACS.SOACS -> String -> FutharkOption
soacsPassOption =
  typedPassOption soacsProg SOACS

kernelsPassOption ::
  Pass GPU.GPU GPU.GPU ->
  String ->
  FutharkOption
kernelsPassOption =
  typedPassOption kernelsProg GPU

kernelsMemPassOption ::
  Pass GPUMem.GPUMem GPUMem.GPUMem ->
  String ->
  FutharkOption
kernelsMemPassOption =
  typedPassOption kernelsMemProg GPUMem

simplifyOption :: String -> FutharkOption
simplifyOption short =
  passOption (passDescription pass) (UntypedPass perform) short long
  where
    perform (SOACS prog) config =
      SOACS <$> runPipeline (onePass simplifySOACS) config prog
    perform (GPU prog) config =
      GPU <$> runPipeline (onePass simplifyGPU) config prog
    perform (MC prog) config =
      MC <$> runPipeline (onePass simplifyMC) config prog
    perform (Seq prog) config =
      Seq <$> runPipeline (onePass simplifySeq) config prog
    perform (SeqMem prog) config =
      SeqMem <$> runPipeline (onePass simplifySeqMem) config prog
    perform (GPUMem prog) config =
      GPUMem <$> runPipeline (onePass simplifyGPUMem) config prog
    perform (MCMem prog) config =
      MCMem <$> runPipeline (onePass simplifyMCMem) config prog

    long = [passLongOption pass]
    pass = simplifySOACS

allocateOption :: String -> FutharkOption
allocateOption short =
  passOption (passDescription pass) (UntypedPass perform) short long
  where
    perform (GPU prog) config =
      GPUMem
        <$> runPipeline (onePass GPU.explicitAllocations) config prog
    perform (Seq prog) config =
      SeqMem
        <$> runPipeline (onePass Seq.explicitAllocations) config prog
    perform s _ =
      externalErrorS $
        "Pass '" ++ passDescription pass ++ "' cannot operate on " ++ representation s

    long = [passLongOption pass]
    pass = Seq.explicitAllocations

iplOption :: String -> FutharkOption
iplOption short =
  passOption (passDescription pass) (UntypedPass perform) short long
  where
    perform (GPU prog) config =
      GPU
        <$> runPipeline (onePass inPlaceLoweringGPU) config prog
    perform (Seq prog) config =
      Seq
        <$> runPipeline (onePass inPlaceLoweringSeq) config prog
    perform s _ =
      externalErrorS $
        "Pass '" ++ passDescription pass ++ "' cannot operate on " ++ representation s

    long = [passLongOption pass]
    pass = inPlaceLoweringSeq

cseOption :: String -> FutharkOption
cseOption short =
  passOption (passDescription pass) (UntypedPass perform) short long
  where
    perform (SOACS prog) config =
      SOACS <$> runPipeline (onePass $ performCSE True) config prog
    perform (GPU prog) config =
      GPU <$> runPipeline (onePass $ performCSE True) config prog
    perform (MC prog) config =
      MC <$> runPipeline (onePass $ performCSE True) config prog
    perform (Seq prog) config =
      Seq <$> runPipeline (onePass $ performCSE True) config prog
    perform (SeqMem prog) config =
      SeqMem <$> runPipeline (onePass $ performCSE False) config prog
    perform (GPUMem prog) config =
      GPUMem <$> runPipeline (onePass $ performCSE False) config prog
    perform (MCMem prog) config =
      MCMem <$> runPipeline (onePass $ performCSE False) config prog

    long = [passLongOption pass]
    pass = performCSE True :: Pass SOACS.SOACS SOACS.SOACS

pipelineOption ::
  (UntypedPassState -> Maybe (Prog fromrep)) ->
  String ->
  (Prog torep -> UntypedPassState) ->
  String ->
  Pipeline fromrep torep ->
  String ->
  [String] ->
  FutharkOption
pipelineOption getprog repdesc repf desc pipeline =
  passOption desc $ UntypedPass pipelinePass
  where
    pipelinePass rep config =
      case getprog rep of
        Just prog ->
          repf <$> runPipeline pipeline config prog
        Nothing ->
          externalErrorS $
            "Expected " ++ repdesc ++ " representation, but got "
              ++ representation rep

soacsPipelineOption ::
  String ->
  Pipeline SOACS.SOACS SOACS.SOACS ->
  String ->
  [String] ->
  FutharkOption
soacsPipelineOption = pipelineOption getSOACSProg "SOACS" SOACS

commandLineOptions :: [FutharkOption]
commandLineOptions =
  [ Option
      "v"
      ["verbose"]
      (OptArg (Right . changeFutharkConfig . incVerbosity) "FILE")
      "Print verbose output on standard error; wrong program to FILE.",
    Option
      []
      ["Werror"]
      (NoArg $ Right $ changeFutharkConfig $ \opts -> opts {futharkWerror = True})
      "Treat warnings as errors.",
    Option
      "w"
      []
      (NoArg $ Right $ changeFutharkConfig $ \opts -> opts {futharkWarn = False})
      "Disable all warnings.",
    Option
      "t"
      ["type-check"]
      ( NoArg $
          Right $ \opts ->
            opts {futharkPipeline = TypeCheck}
      )
      "Print on standard output the type-checked program.",
    Option
      []
      ["no-check"]
      ( NoArg $
          Right $ changeFutharkConfig $ \opts -> opts {futharkTypeCheck = False}
      )
      "Disable type-checking.",
    Option
      []
      ["pretty-print"]
      ( NoArg $
          Right $ \opts ->
            opts {futharkPipeline = PrettyPrint}
      )
      "Parse and pretty-print the AST of the given program.",
    Option
      []
      ["backend"]
      ( ReqArg
          ( \arg -> do
              action <- case arg of
                "c" -> Right $ SeqMemAction compileCAction
                "multicore" -> Right $ MCMemAction compileMulticoreAction
                "opencl" -> Right $ GPUMemAction compileOpenCLAction
                "cuda" -> Right $ GPUMemAction compileCUDAAction
                "wasm" -> Right $ SeqMemAction compileCtoWASMAction
                "wasm-multicore" -> Right $ MCMemAction compileMulticoreToWASMAction
                "python" -> Right $ SeqMemAction compilePythonAction
                "pyopencl" -> Right $ GPUMemAction compilePyOpenCLAction
                _ -> Left $ error $ "Invalid backend: " <> arg

              Right $ \opts -> opts {futharkAction = action}
          )
          "c|multicore|opencl|cuda|python|pyopencl"
      )
      "Run this compiler backend on pipeline result.",
    Option
      []
      ["compile-imperative"]
      ( NoArg $
          Right $ \opts ->
            opts {futharkAction = SeqMemAction $ \_ _ _ -> impCodeGenAction}
      )
      "Translate program into the imperative IL and write it on standard output.",
    Option
      []
      ["compile-imperative-kernels"]
      ( NoArg $
          Right $ \opts ->
            opts {futharkAction = GPUMemAction $ \_ _ _ -> kernelImpCodeGenAction}
      )
      "Translate program into the imperative IL with kernels and write it on standard output.",
    Option
      []
      ["compile-imperative-multicore"]
      ( NoArg $
          Right $ \opts ->
            opts {futharkAction = MCMemAction $ \_ _ _ -> multicoreImpCodeGenAction}
      )
      "Translate program into the imperative IL with kernels and write it on standard output.",
    Option
      "p"
      ["print"]
      (NoArg $ Right $ \opts -> opts {futharkAction = PolyAction printAction})
      "Print the resulting IR (default action).",
    Option
      []
      ["print-aliases"]
      (NoArg $ Right $ \opts -> opts {futharkAction = PolyAction printAliasesAction})
      "Print the resulting IR with aliases.",
    Option
      "m"
      ["metrics"]
      (NoArg $ Right $ \opts -> opts {futharkAction = PolyAction metricsAction})
      "Print AST metrics of the resulting internal representation on standard output.",
    Option
      []
      ["defunctorise"]
      (NoArg $ Right $ \opts -> opts {futharkPipeline = Defunctorise})
      "Partially evaluate all module constructs and print the residual program.",
    Option
      []
      ["monomorphise"]
      (NoArg $ Right $ \opts -> opts {futharkPipeline = Monomorphise})
      "Monomorphise the program.",
    Option
      []
      ["lift-lambdas"]
      (NoArg $ Right $ \opts -> opts {futharkPipeline = LiftLambdas})
      "Lambda-lift the program.",
    Option
      []
      ["defunctionalise"]
      (NoArg $ Right $ \opts -> opts {futharkPipeline = Defunctionalise})
      "Defunctionalise the program.",
    Option
      []
      ["ast"]
      (NoArg $ Right $ \opts -> opts {futharkPrintAST = True})
      "Output ASTs instead of prettyprinted programs.",
    Option
      []
      ["safe"]
      (NoArg $ Right $ changeFutharkConfig $ \opts -> opts {futharkSafe = True})
      "Ignore 'unsafe'.",
    Option
      []
      ["entry-points"]
      ( ReqArg
          ( \arg -> Right $
              changeFutharkConfig $ \opts ->
                opts
                  { futharkEntryPoints = nameFromString arg : futharkEntryPoints opts
                  }
          )
          "NAME"
      )
      "Treat this function as an additional entry point.",
    Option
      []
      ["library"]
      (NoArg $ Right $ \opts -> opts {futharkCompilerMode = ToLibrary})
      "Generate a library instead of an executable.",
    Option
      []
      ["executable"]
      (NoArg $ Right $ \opts -> opts {futharkCompilerMode = ToExecutable})
      "Generate an executable instead of a library (set by default).",
    Option
      []
      ["server"]
      (NoArg $ Right $ \opts -> opts {futharkCompilerMode = ToServer})
      "Generate a server executable.",
    typedPassOption soacsProg Seq firstOrderTransform "f",
    soacsPassOption fuseSOACs "o",
    soacsPassOption inlineFunctions [],
    kernelsPassOption babysitKernels [],
    kernelsPassOption tileLoops [],
    kernelsPassOption unstreamGPU [],
    kernelsPassOption sinkGPU [],
    typedPassOption soacsProg GPU extractKernels [],
    typedPassOption soacsProg MC extractMulticore [],
    iplOption [],
    allocateOption "a",
    kernelsMemPassOption doubleBufferGPU [],
    kernelsMemPassOption expandAllocations [],
    kernelsMemPassOption ReuseAllocations.optimise [],
    cseOption [],
    simplifyOption "e",
    soacsPipelineOption
      "Run the default optimised pipeline"
      standardPipeline
      "s"
      ["standard"],
    pipelineOption
      getSOACSProg
      "GPU"
      GPU
      "Run the default optimised kernels pipeline"
      kernelsPipeline
      []
      ["kernels"],
    pipelineOption
      getSOACSProg
      "GPUMem"
      GPUMem
      "Run the full GPU compilation pipeline"
      gpuPipeline
      []
      ["gpu"],
    pipelineOption
      getSOACSProg
      "GPUMem"
      SeqMem
      "Run the sequential CPU compilation pipeline"
      sequentialCpuPipeline
      []
      ["cpu"],
    pipelineOption
      getSOACSProg
      "MCMem"
      MCMem
      "Run the multicore compilation pipeline"
      multicorePipeline
      []
      ["multicore"]
  ]

incVerbosity :: Maybe FilePath -> FutharkConfig -> FutharkConfig
incVerbosity file cfg =
  cfg {futharkVerbose = (v, file `mplus` snd (futharkVerbose cfg))}
  where
    v = case fst $ futharkVerbose cfg of
      NotVerbose -> Verbose
      Verbose -> VeryVerbose
      VeryVerbose -> VeryVerbose

-- | Entry point.  Non-interactive, except when reading interpreter
-- input from standard input.
main :: String -> [String] -> IO ()
main = mainWithOptions newConfig commandLineOptions "options... program" compile
  where
    compile [file] config =
      Just $ do
        res <-
          runFutharkM (m file config) $
            fst $ futharkVerbose $ futharkConfig config
        case res of
          Left err -> do
            dumpError (futharkConfig config) err
            exitWith $ ExitFailure 2
          Right () -> return ()
    compile _ _ =
      Nothing
    m file config = do
      let p :: (Show a, PP.Pretty a) => [a] -> IO ()
          p =
            mapM_ putStrLn
              . intersperse ""
              . map (if futharkPrintAST config then show else pretty)

          readProgram' = readProgram (futharkEntryPoints (futharkConfig config)) file

      case futharkPipeline config of
        PrettyPrint -> liftIO $ do
          maybe_prog <- parseFuthark file <$> T.readFile file
          case maybe_prog of
            Left err -> fail $ show err
            Right prog
              | futharkPrintAST config -> print prog
              | otherwise -> putStrLn $ pretty prog
        TypeCheck -> do
          (_, imports, _) <- readProgram'
          liftIO $
            forM_ (map snd imports) $ \fm ->
              putStrLn $
                if futharkPrintAST config
                  then show $ fileProg fm
                  else pretty $ fileProg fm
        Defunctorise -> do
          (_, imports, src) <- readProgram'
          liftIO $ p $ evalState (Defunctorise.transformProg imports) src
        Monomorphise -> do
          (_, imports, src) <- readProgram'
          liftIO $
            p $
              flip evalState src $
                Defunctorise.transformProg imports
                  >>= Monomorphise.transformProg
        LiftLambdas -> do
          (_, imports, src) <- readProgram'
          liftIO $
            p $
              flip evalState src $
                Defunctorise.transformProg imports
                  >>= Monomorphise.transformProg
                  >>= LiftLambdas.transformProg
        Defunctionalise -> do
          (_, imports, src) <- readProgram'
          liftIO $
            p $
              flip evalState src $
                Defunctorise.transformProg imports
                  >>= Monomorphise.transformProg
                  >>= LiftLambdas.transformProg
                  >>= Defunctionalise.transformProg
        Pipeline {} -> do
          let (base, ext) = splitExtension file

              readCore parse construct = do
                input <- liftIO $ T.readFile file
                case parse file input of
                  Left err -> externalErrorS $ T.unpack err
                  Right prog ->
                    case checkProg $ Alias.aliasAnalysis prog of
                      Left err -> externalErrorS $ show err
                      Right () -> runPolyPasses config base $ construct prog

              handlers =
                [ ( ".fut",
                    do
                      prog <- runPipelineOnProgram (futharkConfig config) id file
                      runPolyPasses config base (SOACS prog)
                  ),
                  (".fut_soacs", readCore parseSOACS SOACS),
                  (".fut_seq", readCore parseSeq Seq),
                  (".fut_seq_mem", readCore parseSeqMem SeqMem),
                  (".fut_kernels", readCore parseGPU GPU),
                  (".fut_kernels_mem", readCore parseGPUMem GPUMem),
                  (".fut_mc", readCore parseMC MC),
                  (".fut_mc_mem", readCore parseMCMem MCMem)
                ]
          case lookup ext handlers of
            Just handler -> handler
            Nothing ->
              externalErrorS $
                unwords
                  [ "Unsupported extension",
                    show ext,
                    ". Supported extensions:",
                    unwords $ map fst handlers
                  ]

runPolyPasses :: Config -> FilePath -> UntypedPassState -> FutharkM ()
runPolyPasses config base initial_prog = do
  end_prog <-
    foldM
      (runPolyPass pipeline_config)
      initial_prog
      (getFutharkPipeline config)
  case (end_prog, futharkAction config) of
    (SOACS prog, SOACSAction action) ->
      otherAction action prog
    (GPU prog, GPUAction action) ->
      otherAction action prog
    (SeqMem prog, SeqMemAction action) ->
      backendAction prog action
    (GPUMem prog, GPUMemAction action) ->
      backendAction prog action
    (MCMem prog, MCMemAction action) ->
      backendAction prog action
    (SOACS soacs_prog, PolyAction acs) ->
      otherAction acs soacs_prog
    (GPU kernels_prog, PolyAction acs) ->
      otherAction acs kernels_prog
    (MC mc_prog, PolyAction acs) ->
      otherAction acs mc_prog
    (Seq seq_prog, PolyAction acs) ->
      otherAction acs seq_prog
    (GPUMem mem_prog, PolyAction acs) ->
      otherAction acs mem_prog
    (SeqMem mem_prog, PolyAction acs) ->
      otherAction acs mem_prog
    (MCMem mem_prog, PolyAction acs) ->
      otherAction acs mem_prog
    (_, action) ->
      externalErrorS $
        "Action expects "
          ++ representation action
          ++ " representation, but got "
          ++ representation end_prog
          ++ "."
  logMsg ("Done." :: String)
  where
    backendAction prog actionf = do
      let action = actionf (futharkConfig config) (futharkCompilerMode config) base
      otherAction action prog

    otherAction action prog = do
      logMsg $ "Running action " ++ actionName action
      actionProcedure action prog

    pipeline_config =
      PipelineConfig
        { pipelineVerbose = fst (futharkVerbose $ futharkConfig config) > NotVerbose,
          pipelineValidate = futharkTypeCheck $ futharkConfig config
        }

runPolyPass ::
  PipelineConfig ->
  UntypedPassState ->
  UntypedPass ->
  FutharkM UntypedPassState
runPolyPass pipeline_config s (UntypedPass f) =
  f s pipeline_config
