{-# LANGUAGE QuasiQuotes #-}
{-# LANGUAGE TemplateHaskell #-}

--

-- | C code generator.  This module can convert a correct ImpCode
-- program to an equivalent C program.  This C program is expected to
-- be converted to WebAssembly, so we also produce the intended
-- JavaScript wrapper.
module Futhark.CodeGen.Backends.MulticoreWASM
  ( compileProg,
    runServer,
    GC.CParts (..),
    GC.asLibrary,
    GC.asExecutable,
    GC.asServer,
  )
where

--import Language.Futhark.Core (nameToString) -- TODO (see if might be useful later)

import Data.FileEmbed
import Data.Maybe
import qualified Futhark.CodeGen.Backends.GenericC as GC
import Futhark.CodeGen.Backends.GenericWASM
import qualified Futhark.CodeGen.Backends.MulticoreC as MC
import qualified Futhark.CodeGen.ImpCode.Multicore as Imp
import qualified Futhark.CodeGen.ImpGen.Multicore as ImpGen
import Futhark.IR.MCMem
import Futhark.MonadFreshNames
import qualified Language.C.Quote.OpenCL as C

compileProg :: MonadFreshNames m => Prog MCMem -> m (ImpGen.Warnings, (GC.CParts, String, [String]))
compileProg prog = do
  (ws, prog') <- ImpGen.compileProg prog

  prog'' <-
    GC.compileProg
      "wasm_multicore"
      MC.operations
      generateContext
      ""
      [DefaultSpace]
      MC.cliOptions
      prog'

  pure
    ( ws,
      ( prog'',
        javascriptWrapper (fRepMyRep prog'),
        "_futhark_context_config_set_num_threads" : emccExportNames (fRepMyRep prog')
      )
    )
  where
    generateContext = do
      let scheduler_h = $(embedStringFile "rts/c/scheduler.h")
      mapM_ GC.earlyDecl [C.cunit|$esc:scheduler_h|]

      cfg <- GC.publicDef "context_config" GC.InitDecl $ \s ->
        ( [C.cedecl|struct $id:s;|],
          [C.cedecl|struct $id:s { int debugging;
                                   int profiling;
                                   int num_threads;
                                 };|]
        )

      GC.publicDef_ "context_config_new" GC.InitDecl $ \s ->
        ( [C.cedecl|struct $id:cfg* $id:s(void);|],
          [C.cedecl|struct $id:cfg* $id:s(void) {
                                 struct $id:cfg *cfg = (struct $id:cfg*) malloc(sizeof(struct $id:cfg));
                                 if (cfg == NULL) {
                                   return NULL;
                                 }
                                 cfg->debugging = 0;
                                 cfg->profiling = 0;
                                 cfg->num_threads = 0;
                                 return cfg;
                               }|]
        )

      GC.publicDef_ "context_config_free" GC.InitDecl $ \s ->
        ( [C.cedecl|void $id:s(struct $id:cfg* cfg);|],
          [C.cedecl|void $id:s(struct $id:cfg* cfg) {
                                 free(cfg);
                               }|]
        )

      GC.publicDef_ "context_config_set_debugging" GC.InitDecl $ \s ->
        ( [C.cedecl|void $id:s(struct $id:cfg* cfg, int flag);|],
          [C.cedecl|void $id:s(struct $id:cfg* cfg, int detail) {
                          cfg->debugging = detail;
                        }|]
        )

      GC.publicDef_ "context_config_set_profiling" GC.InitDecl $ \s ->
        ( [C.cedecl|void $id:s(struct $id:cfg* cfg, int flag);|],
          [C.cedecl|void $id:s(struct $id:cfg* cfg, int flag) {
                          cfg->profiling = flag;
                        }|]
        )

      GC.publicDef_ "context_config_set_logging" GC.InitDecl $ \s ->
        ( [C.cedecl|void $id:s(struct $id:cfg* cfg, int flag);|],
          [C.cedecl|void $id:s(struct $id:cfg* cfg, int detail) {
                                 /* Does nothing for this backend. */
                                 (void)cfg; (void)detail;
                               }|]
        )

      GC.publicDef_ "context_config_set_num_threads" GC.InitDecl $ \s ->
        ( [C.cedecl|void $id:s(struct $id:cfg *cfg, int n);|],
          [C.cedecl|void $id:s(struct $id:cfg *cfg, int n) {
                                 cfg->num_threads = n;
                               }|]
        )

      (fields, init_fields) <- GC.contextContents

      ctx <- GC.publicDef "context" GC.InitDecl $ \s ->
        ( [C.cedecl|struct $id:s;|],
          [C.cedecl|struct $id:s {
                          struct scheduler scheduler;
                          int detail_memory;
                          int debugging;
                          int profiling;
                          int profiling_paused;
                          int logging;
                          typename lock_t lock;
                          char *error;
                          typename FILE *log;
                          int total_runs;
                          long int total_runtime;
                          $sdecls:fields

                          // Tuning parameters
                          typename int64_t tuning_timing;
                          typename int64_t tuning_iter;
                        };|]
        )

      GC.publicDef_ "context_new" GC.InitDecl $ \s ->
        ( [C.cedecl|struct $id:ctx* $id:s(struct $id:cfg* cfg);|],
          [C.cedecl|struct $id:ctx* $id:s(struct $id:cfg* cfg) {
                 struct $id:ctx* ctx = (struct $id:ctx*) malloc(sizeof(struct $id:ctx));
                 if (ctx == NULL) {
                   return NULL;
                 }

                 // Initialize rand()
                 fast_srand(time(0));
                 ctx->detail_memory = cfg->debugging;
                 ctx->debugging = cfg->debugging;
                 ctx->profiling = cfg->profiling;
                 ctx->profiling_paused = 0;
                 ctx->logging = 0;
                 ctx->error = NULL;
                 ctx->log = stderr;
                 create_lock(&ctx->lock);

                 int tune_kappa = 0;
                 double kappa = 5.1f * 1000;

                 if (tune_kappa) {
                   if (determine_kappa(&kappa) != 0) {
                     return NULL;
                   }
                 }

                 if (scheduler_init(&ctx->scheduler,
                                    cfg->num_threads > 0 ?
                                    cfg->num_threads : num_processors(),
                                    kappa) != 0) {
                   return NULL;
                 }

                 $stms:init_fields

                 init_constants(ctx);

                 return ctx;
              }|]
        )

      GC.publicDef_ "context_free" GC.InitDecl $ \s ->
        ( [C.cedecl|void $id:s(struct $id:ctx* ctx);|],
          [C.cedecl|void $id:s(struct $id:ctx* ctx) {
                 free_constants(ctx);
                 (void)scheduler_destroy(&ctx->scheduler);
                 free_lock(&ctx->lock);
                 free(ctx);
               }|]
        )

      GC.publicDef_ "context_sync" GC.InitDecl $ \s ->
        ( [C.cedecl|int $id:s(struct $id:ctx* ctx);|],
          [C.cedecl|int $id:s(struct $id:ctx* ctx) {
                                 (void)ctx;
                                 return 0;
                               }|]
        )

      GC.earlyDecl [C.cedecl|static const char *size_names[0];|]
      GC.earlyDecl [C.cedecl|static const char *size_vars[0];|]
      GC.earlyDecl [C.cedecl|static const char *size_classes[0];|]

      GC.publicDef_ "context_config_set_size" GC.InitDecl $ \s ->
        ( [C.cedecl|int $id:s(struct $id:cfg* cfg, const char *size_name, size_t size_value);|],
          [C.cedecl|int $id:s(struct $id:cfg* cfg, const char *size_name, size_t size_value) {
                         (void)cfg; (void)size_name; (void)size_value;
                         return 1;
                       }|]
        )

fRepMyRep :: Imp.Definitions Imp.Multicore -> [JSEntryPoint]
fRepMyRep prog =
  let Imp.Functions fs = Imp.defFuns prog
      function (Imp.Function entry _ _ _ res args) = do
        n <- entry
        Just $
          JSEntryPoint
            { name = nameToString n,
              parameters = map extToString args,
              ret = map extToString res
            }
   in mapMaybe (function . snd) fs
