{-# LANGUAGE QuasiQuotes, FlexibleContexts #-}
module Futhark.CodeGen.Backends.COpenCL
  ( compileProg
  ) where

import Control.Applicative
import Control.Monad
import Data.List

import Prelude

import qualified Language.C.Syntax as C
import qualified Language.C.Quote.OpenCL as C

import Futhark.Representation.ExplicitMemory (Prog)
import Futhark.CodeGen.Backends.COpenCL.Boilerplate
import qualified Futhark.CodeGen.Backends.GenericC as GenericC
import Futhark.CodeGen.Backends.GenericC.Options
import Futhark.CodeGen.ImpCode.OpenCL
import qualified Futhark.CodeGen.ImpGen.OpenCL as ImpGen
import Futhark.MonadFreshNames

compileProg :: Prog -> Either String String
compileProg prog = do
  Program opencl_code kernel_names prog' <- ImpGen.compileProg prog
  let header = unlines [ "#include <CL/cl.h>\n"
                       , "#define FUT_KERNEL(s) #s"
                       , "#define OPENCL_SUCCEED(e) opencl_succeed(e, #e, __FILE__, __LINE__)"
                       , blockDimPragma
                       ]
  return $
    header ++
    GenericC.compileProg operations ()
    (openClDecls kernel_names opencl_code)
    openClInit (openClReport kernel_names) options prog'
  where operations :: GenericC.Operations OpenCL ()
        operations = GenericC.Operations
                     { GenericC.opsCompiler = callKernel
                     , GenericC.opsWriteScalar = writeOpenCLScalar
                     , GenericC.opsReadScalar = readOpenCLScalar
                     , GenericC.opsAllocate = allocateOpenCLBuffer
                     , GenericC.opsCopy = copyOpenCLMemory
                     , GenericC.opsMemoryType = openclMemoryType
                     }

        options = [ Option { optionLongName = "platform"
                           , optionShortName = Just 'p'
                           , optionArgument = RequiredArgument
                           , optionAction = [C.cstm|cl_preferred_platform = optarg;|]
                           }
                  , Option { optionLongName = "device"
                           , optionShortName = Just 'd'
                           , optionArgument = RequiredArgument
                           , optionAction = [C.cstm|cl_preferred_device = optarg;|]
                           }
                  ]

writeOpenCLScalar :: GenericC.WriteScalar OpenCL ()
writeOpenCLScalar mem i t "device" val = do
  val' <- newVName "write_tmp"
  GenericC.stm [C.cstm|{
                   $ty:t $id:val' = $exp:val;
                   assert(clEnqueueWriteBuffer(fut_cl_queue, $id:mem, CL_TRUE,
                                               $exp:i, sizeof($ty:t),
                                               &$id:val',
                                               0, NULL, NULL)
                          == CL_SUCCESS);
                   assert(clFinish(fut_cl_queue) == CL_SUCCESS);
                }|]
writeOpenCLScalar _ _ _ space _ =
  fail $ "Cannot write to '" ++ space ++ "' memory space."

readOpenCLScalar :: GenericC.ReadScalar OpenCL ()
readOpenCLScalar mem i t "device" = do
  val <- newVName "read_res"
  GenericC.decl [C.cdecl|$ty:t $id:val;|]
  GenericC.stm [C.cstm|{
                 assert(clEnqueueReadBuffer(fut_cl_queue, $id:mem, CL_TRUE,
                                            $exp:i, sizeof($ty:t),
                                            &$id:val,
                                            0, NULL, NULL)
                        == CL_SUCCESS);
                 assert(clFinish(fut_cl_queue) == CL_SUCCESS);
              }|]
  return [C.cexp|$id:val|]
readOpenCLScalar _ _ _ space =
  fail $ "Cannot read from '" ++ space ++ "' memory space."

allocateOpenCLBuffer :: GenericC.Allocate OpenCL ()
allocateOpenCLBuffer mem size "device" = do

  errorname <- newVName "clCreateBuffer_succeeded"
  -- clCreateBuffer fails with CL_INVALID_BUFFER_SIZE if we pass 0 as
  -- the size (unlike malloc()), so we make sure we always allocate at
  -- least a single byte.  The alternative is to protect this with a
  -- branch and leave the cl_mem variable uninitialised if the size is
  -- zero, but this would leave sort of a landmine around, that would
  -- blow up if we ever passed it to an OpenCL function.
  GenericC.stm [C.cstm|{
    typename cl_int $id:errorname;
    $id:mem = clCreateBuffer(fut_cl_context, CL_MEM_READ_WRITE,
                             $exp:size > 0 ? $exp:size : 1, NULL,
                             &$id:errorname);
    assert($id:errorname == 0);
  }|]
allocateOpenCLBuffer _ _ space =
  fail $ "Cannot allocate in '" ++ space ++ "' space"

copyOpenCLMemory :: GenericC.Copy OpenCL ()
-- The read/write/copy-buffer functions fail if the given offset is
-- out of bounds, even if asked to read zero bytes.  We protect with a
-- branch to avoid this.
copyOpenCLMemory destmem destidx DefaultSpace srcmem srcidx (Space "device") nbytes =
  GenericC.stm [C.cstm|{
    if ($exp:nbytes > 0) {
      assert(clEnqueueReadBuffer(fut_cl_queue, $id:srcmem, CL_TRUE,
                                 $exp:srcidx, $exp:nbytes,
                                 $id:destmem + $exp:destidx,
                                 0, NULL, NULL)
             == CL_SUCCESS);
      assert(clFinish(fut_cl_queue) == CL_SUCCESS);
   }
  }|]
copyOpenCLMemory destmem destidx (Space "device") srcmem srcidx DefaultSpace nbytes =
  GenericC.stm [C.cstm|{
    if ($exp:nbytes > 0) {
      assert(clEnqueueWriteBuffer(fut_cl_queue, $id:destmem, CL_TRUE,
                                  $exp:destidx, $exp:nbytes,
                                  $id:srcmem + $exp:srcidx,
                                  0, NULL, NULL)
             == CL_SUCCESS);
      assert(clFinish(fut_cl_queue) == CL_SUCCESS);
    }
  }|]
copyOpenCLMemory destmem destidx (Space "device") srcmem srcidx (Space "device") nbytes =
  -- Be aware that OpenCL swaps the usual order of operands for
  -- memcpy()-like functions.  The order below is not a typo.
  GenericC.stm [C.cstm|{
    if ($exp:nbytes > 0) {
      assert(clEnqueueCopyBuffer(fut_cl_queue,
                                 $id:srcmem, $id:destmem,
                                 $exp:srcidx, $exp:destidx,
                                 $exp:nbytes,
                                 0, NULL, NULL)
             == CL_SUCCESS);
      assert(clFinish(fut_cl_queue) == CL_SUCCESS);
    }
  }|]
copyOpenCLMemory _ _ destspace _ _ srcspace _ =
  error $ "Cannot copy to " ++ show destspace ++ " from " ++ show srcspace

openclMemoryType :: GenericC.MemoryType OpenCL ()
openclMemoryType "device" = pure [C.cty|typename cl_mem|]
openclMemoryType "local" = pure [C.cty|unsigned char|] -- dummy type
openclMemoryType space =
  fail $ "OpenCL backend does not support '" ++ space ++ "' memory space."

callKernel :: GenericC.OpCompiler OpenCL ()
callKernel (LaunchKernel name args kernel_size workgroup_size) = do
  zipWithM_ setKernelArg [(0::Int)..] args
  kernel_size' <- mapM GenericC.compileExp kernel_size
  workgroup_size' <- case workgroup_size of
    Nothing -> return Nothing
    Just es -> Just <$> mapM GenericC.compileExp es
  launchKernel name kernel_size' workgroup_size'
  return GenericC.Done
  where setKernelArg i (ValueArg e bt) = do
          v <- GenericC.compileExpToName "kernel_arg" bt e
          GenericC.stm [C.cstm|
            assert(clSetKernelArg($id:name, $int:i, sizeof($id:v), &$id:v)
                   == CL_SUCCESS);
          |]

        setKernelArg i (MemArg v) =
          GenericC.stm [C.cstm|
            assert(clSetKernelArg($id:name, $int:i, sizeof($id:v), &$id:v)
                   == CL_SUCCESS);
          |]

        setKernelArg i (SharedMemoryArg num_bytes) = do
          num_bytes' <- GenericC.compileExp $ innerExp num_bytes
          GenericC.stm [C.cstm|
            assert(clSetKernelArg($id:name, $int:i, $exp:num_bytes', NULL)
                   == CL_SUCCESS);
            |]

launchKernel :: C.ToExp a =>
                String -> [a] -> Maybe [a] -> GenericC.CompilerM op s ()
launchKernel kernel_name kernel_dims workgroup_dims = do
  global_work_size <- newVName "global_work_size"
  time_start <- newVName "time_start"
  time_end <- newVName "time_end"
  time_diff <- newVName "time_diff"

  local_work_size_arg <- case workgroup_dims of
    Nothing ->
      return [C.cexp|NULL|]
    Just es -> do
      local_work_size <- newVName "local_work_size"
      let workgroup_dims' = map toInit es
      GenericC.decl [C.cdecl|const size_t $id:local_work_size[$int:kernel_rank] = {$inits:workgroup_dims'};|]
      return [C.cexp|$id:local_work_size|]

  GenericC.stm [C.cstm|{
    if ($exp:total_elements != 0) {
      const size_t $id:global_work_size[$int:kernel_rank] = {$inits:kernel_dims'};
      struct timeval $id:time_start, $id:time_end, $id:time_diff;
      fprintf(stderr, "kernel size %s: [", $string:(textual global_work_size));
      $stms:(printKernelSize global_work_size)
      fprintf(stderr, "]\n");
      gettimeofday(&$id:time_start, NULL);
      OPENCL_SUCCEED(
        clEnqueueNDRangeKernel(fut_cl_queue, $id:kernel_name, $int:kernel_rank, NULL,
                               $id:global_work_size, $exp:local_work_size_arg,
                               0, NULL, NULL));
      OPENCL_SUCCEED(clFinish(fut_cl_queue));
      gettimeofday(&$id:time_end, NULL);
      timeval_subtract(&$id:time_diff, &$id:time_end, &$id:time_start);
      $id:kernel_total_runtime += $id:time_diff.tv_sec*1e6+$id:time_diff.tv_usec;
      $id:kernel_runs++;
      fprintf(stderr, "kernel %s runtime: %dus\n",
              $string:kernel_name,
              (int)(($id:time_diff.tv_sec*1e6+$id:time_diff.tv_usec)));
    }
    }|]
  where kernel_total_runtime = kernel_name ++ "_total_runtime"
        kernel_runs = kernel_name ++ "_runs"
        kernel_rank = length kernel_dims
        kernel_dims' = map toInit kernel_dims
        total_elements = foldl multExp [C.cexp|1|] kernel_dims

        toInit e = [C.cinit|$exp:e|]
        multExp x y = [C.cexp|$exp:x * $exp:y|]

        printKernelSize :: VName -> [C.Stm]
        printKernelSize global_work_size =
          intercalate [[C.cstm|fprintf(stderr, ", ");|]] $
          map (printKernelDim global_work_size) [0..kernel_rank-1]
        printKernelDim global_work_size i =
          [[C.cstm|fprintf(stderr, "%zu", $id:global_work_size[$int:i]);|]]

blockDimPragma :: String
blockDimPragma = "#define FUT_BLOCK_DIM " ++ show (transposeBlockDim :: Int)
