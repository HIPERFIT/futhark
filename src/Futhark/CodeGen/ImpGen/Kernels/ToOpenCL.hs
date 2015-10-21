{-# LANGUAGE QuasiQuotes #-}
-- | This module defines a translation from imperative code with
-- kernels to imperative code with OpenCL calls.
module Futhark.CodeGen.ImpGen.Kernels.ToOpenCL
  ( kernelsToOpenCL
  )
  where

import Control.Applicative
import Control.Monad.State
import Data.List
import Data.Monoid
import qualified Data.HashSet as HS

import qualified Language.C.Syntax as C
import qualified Language.C.Quote.OpenCL as C

import qualified Futhark.CodeGen.OpenCL.Kernels as Kernels
import qualified Futhark.CodeGen.Backends.GenericC as GenericC
import Futhark.CodeGen.Backends.SimpleRepresentation
import Futhark.CodeGen.ImpCode.Kernels hiding (Program)
import qualified Futhark.CodeGen.ImpCode.Kernels as ImpKernels
import Futhark.CodeGen.ImpCode.OpenCL hiding (Program)
import qualified Futhark.CodeGen.ImpCode.OpenCL as ImpOpenCL
import Futhark.MonadFreshNames
import Futhark.Util.Pretty (pretty)

-- | Translate a kernels-program to an OpenCL-program.
kernelsToOpenCL :: ImpKernels.Program
                -> Either String ImpOpenCL.Program
kernelsToOpenCL prog = do
  (kernels, requirements) <- compileKernels $ getKernels prog
  let kernel_names = map fst kernels
      opencl_code = pretty $ openClCode kernels requirements
  return $ ImpOpenCL.Program
    opencl_code
    kernel_names $
    fmap callKernel $ prog

pointerQuals ::  Monad m => String -> m [C.TypeQual]
pointerQuals "global"     = return [C.ctyquals|__global|]
pointerQuals "local"      = return [C.ctyquals|__local volatile|]
pointerQuals "private"    = return [C.ctyquals|__private|]
pointerQuals "constant"   = return [C.ctyquals|__constant|]
pointerQuals "write_only" = return [C.ctyquals|__write_only|]
pointerQuals "read_only"  = return [C.ctyquals|__read_only|]
pointerQuals "kernel"     = return [C.ctyquals|__kernel|]
pointerQuals s            = fail $ "'" ++ s ++ "' is not an OpenCL kernel address space."

type UsedFunctions = [(String,C.Func)] -- The ordering is important!

data OpenClRequirements =
  OpenClRequirements { _kernelUsedFunctions :: UsedFunctions
                     , _kernelPragmas :: [String]
                     }

instance Monoid OpenClRequirements where
  mempty =
    OpenClRequirements [] []

  OpenClRequirements used1 pragmas1 `mappend` OpenClRequirements used2 pragmas2 =
    OpenClRequirements (nubBy cmpFst $ used1 <> used2) (nub $ pragmas1 ++ pragmas2)
    where cmpFst (x, _) (y, _) = x == y

inKernelOperations :: GenericC.Operations InKernel UsedFunctions
inKernelOperations = GenericC.Operations
                     { GenericC.opsCompiler = kernelOps
                     , GenericC.opsMemoryType = kernelMemoryType
                     , GenericC.opsWriteScalar = GenericC.writeScalarPointerWithQuals pointerQuals
                     , GenericC.opsReadScalar = GenericC.readScalarPointerWithQuals pointerQuals
                     , GenericC.opsAllocate = cannotAllocate
                     , GenericC.opsCopy = copyInKernel
                     }
  where kernelOps :: GenericC.OpCompiler InKernel UsedFunctions
        kernelOps (GetGroupId v i) = do
          GenericC.stm [C.cstm|$id:v = get_group_id($int:i);|]
          return GenericC.Done
        kernelOps (GetLocalId v i) = do
          GenericC.stm [C.cstm|$id:v = get_local_id($int:i);|]
          return GenericC.Done
        kernelOps (GetLocalSize v i) = do
          GenericC.stm [C.cstm|$id:v = get_local_size($int:i);|]
          return GenericC.Done
        kernelOps (GetGlobalId v i) = do
          GenericC.stm [C.cstm|$id:v = get_global_id($int:i);|]
          return GenericC.Done
        kernelOps (GetGlobalSize v i) = do
          GenericC.stm [C.cstm|$id:v = get_global_size($int:i);|]
          return GenericC.Done

        cannotAllocate :: GenericC.Allocate InKernel UsedFunctions
        cannotAllocate _ =
          fail "Cannot allocate memory in kernel"

        copyInKernel :: GenericC.Copy InKernel UsedFunctions
        copyInKernel _ _ _ _ _ _ _ =
          fail $ "Cannot bulk copy in kernel."

        kernelMemoryType space = do
          quals <- pointerQuals space
          return [C.cty|$tyquals:quals $ty:defaultMemBlockType|]

compileKernels :: [CallKernel] -> Either String ([(String, C.Func)], OpenClRequirements)
compileKernels kernels = do
  (funcs, reqs) <- unzip <$> mapM compileKernel kernels
  return (concat funcs, mconcat reqs)

compileKernel :: CallKernel -> Either String ([(String, C.Func)], OpenClRequirements)
compileKernel (Kernel kernel) =
  let (funbody, s) =
        GenericC.runCompilerM (Functions []) inKernelOperations blankNameSource mempty $
        GenericC.collect $ GenericC.compileCode $ kernelBody kernel

      used_funs = GenericC.compUserState s

      params = map useAsParam $ kernelUses kernel

      kernel_funs = functionsCalled $ kernelBody kernel

  in Right ([(mapKernelName kernel,
             [C.cfun|__kernel void $id:(mapKernelName kernel) ($params:params) {
                 const uint $id:(kernelThreadNum kernel) = get_global_id(0);
                 $items:funbody
             }|])],
            OpenClRequirements (used_funs ++ requiredFunctions kernel_funs) [])

compileKernel (Reduce kernel) =
  let ((kernel_prologue, fold_body, red_body,
        write_fold_result, write_final_result), s) =
        GenericC.runCompilerM (Functions []) inKernelOperations blankNameSource mempty $ do
          kernel_prologue_ <-
            GenericC.collect $ GenericC.compileCode $ reductionPrologue kernel
          fold_body_ <-
            GenericC.collect $ GenericC.compileCode $ reductionFoldOperation kernel
          red_body_ <-
            GenericC.collect $ GenericC.compileCode $ reductionReduceOperation kernel
          write_fold_result_ <-
            GenericC.collect $ GenericC.compileCode $ reductionWriteFoldResult kernel

          write_final_result_ <-
            GenericC.collect $ GenericC.compileCode $ reductionWriteFinalResult kernel

          return (kernel_prologue_, fold_body_, red_body_,
                  write_fold_result_, write_final_result_)

      used_funs = GenericC.compUserState s

      use_params = map useAsParam $ reductionUses kernel

      kernel_funs = functionsCalled (reductionReduceOperation kernel) <>
                    functionsCalled (reductionFoldOperation kernel)

      local_memory_params =
        flip evalState (blankNameSource :: VNameSource) $
        mapM prepareLocalMemory $ reductionThreadLocalMemory kernel

      prologue = kernel_prologue

      opencl_kernel =
        Kernels.reduce Kernels.Reduction
         { Kernels.reductionKernelName =
            reduceKernelName kernel
         , Kernels.reductionOffsetName =
             textual $ reductionOffsetName kernel
         , Kernels.reductionInputArrayIndexName =
             textual $ reductionKernelName kernel

         , Kernels.reductionPrologue = prologue
         , Kernels.reductionFoldOperation = fold_body
         , Kernels.reductionWriteFoldResult = write_fold_result
         , Kernels.reductionReduceOperation = red_body
         , Kernels.reductionWriteFinalResult = write_final_result

         , Kernels.reductionKernelArgs =
             local_memory_params ++ use_params
         }

  in Right ([(reduceKernelName kernel, opencl_kernel)],
            OpenClRequirements (used_funs ++ requiredFunctions kernel_funs) [])
  where prepareLocalMemory (mem, _) =
          return ([C.cparam|__local volatile unsigned char* restrict $id:mem|])

compileKernel kernel@(MapTranspose bt _ _ _ _ _ _ _) =
  Right ([(kernelName kernel, Kernels.mapTranspose (kernelName kernel) ty)],
         mempty)
  where ty = GenericC.scalarTypeToCType bt

useAsParam :: KernelUse -> C.Param
useAsParam (ScalarUse name bt) =
  let ctp = GenericC.scalarTypeToCType bt
  in [C.cparam|$ty:ctp $id:name|]
useAsParam (MemoryUse name _) =
  [C.cparam|__global unsigned char *$id:name|]

requiredFunctions :: HS.HashSet Name -> [(String, C.Func)]
requiredFunctions kernel_funs =
  let used_in_kernel = (`HS.member` kernel_funs) . nameFromString . fst
      funs32_used = filter used_in_kernel funs32
      funs64_used = filter used_in_kernel funs64

      funs32 = [("toFloat32", c_toFloat32),
                ("trunc32", c_trunc32),
                ("log32", c_log32),
                ("sqrt32", c_sqrt32),
                ("exp32", c_exp32)]

      funs64 = [("toFloat64", c_toFloat64),
                ("trunc64", c_trunc64),
                ("log64", c_log64),
                ("sqrt64", c_sqrt64),
                ("exp64", c_exp64)]
  in funs32_used ++ funs64_used

openClProgramHeader :: OpenClRequirements -> [C.Definition]
openClProgramHeader (OpenClRequirements used_funs pragmas) =
  [ [C.cedecl|$esc:pragma|] | pragma <- pragmas ] ++
  [ [C.cedecl|$func:used_fun|] | (_, used_fun) <- used_funs ]

openClCode :: [(String, C.Func)] -> OpenClRequirements -> [C.Definition]
openClCode kernels requirements =
  [C.cunit|
// Program header and utility functions
   $edecls:header

// Kernel definitions
   $edecls:funcs
          |]
  where header =
          openClProgramHeader requirements
        funcs =
          [[C.cedecl|$func:kernel_func|] |
           (_, kernel_func) <- kernels ]


mapKernelName :: MapKernel -> String
mapKernelName = ("map_kernel_"++) . show . baseTag . kernelThreadNum

reduceKernelName :: ReduceKernel -> String
reduceKernelName = ("red_kernel_"++) . show . baseTag . reductionKernelName

kernelName :: CallKernel -> String
kernelName (Kernel k) =
  mapKernelName k
kernelName (Reduce k) =
  reduceKernelName k
kernelName (MapTranspose bt _ _ _ _ _ _ _) =
  "fut_kernel_map_transpose_" ++ pretty bt

callKernel :: CallKernel -> OpenCL
callKernel kernel =
  LaunchKernel
  (kernelName kernel) (kernelArgs kernel) kernel_size workgroup_size
  where (kernel_size, workgroup_size) = kernelAndWorkgroupSize kernel

kernelArgs :: CallKernel -> [KernelArg]
kernelArgs (Kernel kernel) =
  map useToArg $ kernelUses kernel
kernelArgs (Reduce kernel) =
  map (SharedMemoryArg . memSizeToExp . snd)
      (reductionThreadLocalMemory kernel) ++
  map useToArg (reductionUses kernel)
kernelArgs (MapTranspose bt destmem destoffset srcmem srcoffset _ x_elems y_elems) =
  [ MemArg destmem
  , ValueArg destoffset Int
  , MemArg srcmem
  , ValueArg srcoffset Int
  , ValueArg x_elems Int
  , ValueArg y_elems Int
  , SharedMemoryArg shared_memory
  ]
  where shared_memory =
          bytes $ (transposeBlockDim + 1) * transposeBlockDim * SizeOf bt

kernelAndWorkgroupSize :: CallKernel -> ([Exp], Maybe [Exp])
kernelAndWorkgroupSize (Kernel kernel) =
  ([sizeToExp $ kernelSize kernel],
   Nothing)
kernelAndWorkgroupSize (Reduce kernel) =
  ([sizeToExp (reductionNumGroups kernel) *
    sizeToExp (reductionGroupSize kernel)],
   Just [sizeToExp $ reductionGroupSize kernel])
kernelAndWorkgroupSize (MapTranspose _ _ _ _ _ num_arrays x_elems y_elems) =
  ([roundedToBlockDim x_elems,
    roundedToBlockDim y_elems,
    roundedToBlockDim num_arrays],
   Just [transposeBlockDim, transposeBlockDim, 1])
  where roundedToBlockDim e =
          e + ((transposeBlockDim -
                (e `impRem` transposeBlockDim)) `impRem`
               transposeBlockDim)
        impRem = BinOp Rem

useToArg :: KernelUse -> KernelArg
useToArg (MemoryUse mem _) = MemArg mem
useToArg (ScalarUse v bt)  = ValueArg (ScalarVar v) bt
