{-# LANGUAGE FlexibleContexts #-}
module Futhark.CodeGen.Backends.PyOpenCL
  ( compileProg
  ) where

import Control.Applicative
import Control.Monad
import Data.List

import Prelude

import Futhark.Representation.AST.Attributes.Constants
import Futhark.Representation.ExplicitMemory (Prog)
import Futhark.CodeGen.Backends.PyOpenCL.Boilerplate
import qualified Futhark.CodeGen.Backends.GenericPython as Py
import qualified Futhark.CodeGen.ImpCode.OpenCL as Imp
import qualified Futhark.CodeGen.ImpGen.OpenCL as ImpGen
import Futhark.CodeGen.Backends.GenericPython.AST
import Futhark.Util.Pretty(pretty)
import Futhark.MonadFreshNames

import Futhark.CodeGen.Backends.GenericPython.Definitions

--maybe pass the config file rather than multiple arguments
compileProg :: MonadFreshNames m => Maybe String -> Prog ->  m (Either String String)
compileProg module_name prog = do
  res <- ImpGen.compileProg prog
  --could probably be a better why do to this..
  case res of
    Left err -> return $ Left err
    Right (Imp.Program opencl_code opencl_prelude kernel_names prog')  -> do
      --prepare the strings for assigning the kernels and set them as global
      let assign = unlines $ map (\x -> pretty $ Assign (Var ("self."++x++"_var")) (Var $ "program."++x)) kernel_names

      let defines =
            [Assign (Var "FUT_BLOCK_DIM") $ StringLiteral $ show (Imp.transposeBlockDim :: Int),
             Assign (Var "cl_group_size") $ Constant $ value (512::Int32),
             Assign (Var "synchronous") $ Constant $ value False,
             Assign (Var "fut_opencl_src") $ RawStringLiteral $ opencl_prelude ++ opencl_code,
             Escape pyTestMain]
      let imports = [Import "sys" Nothing,
                     Import "numpy" $ Just "np",
                     Import "ctypes" $ Just "ct",
                     Import "pyopencl" $ Just "cl",
                     Import "time" Nothing]

      let constructor = Py.Constructor ["self"] [Escape $ openClInit assign]

      Right <$> Py.compileProg module_name constructor imports defines operations ()
        [Exp $ Call "self.queue.finish" []] [] prog'
  where operations :: Py.Operations Imp.OpenCL ()
        operations = Py.Operations
                     { Py.opsCompiler = callKernel
                     , Py.opsWriteScalar = writeOpenCLScalar
                     , Py.opsReadScalar = readOpenCLScalar
                     , Py.opsAllocate = allocateOpenCLBuffer
                     , Py.opsCopy = copyOpenCLMemory
                     }

-- We have many casts to 'long', because PyOpenCL may get confused at
-- the 32-bit numbers that ImpCode uses for offsets and the like.
asLong :: PyExp -> PyExp
asLong x = Call "long" [Arg x]

callKernel :: Py.OpCompiler Imp.OpenCL ()
callKernel (Imp.GetNumGroups v) = do
  Py.stm $ Assign (Var (textual v)) $ Constant $ value (128::Int32)
  return Py.Done

callKernel (Imp.GetGroupSize v) = do
  Py.stm $ Assign (Var (textual v)) $ Constant $ value (512::Int32)
  return Py.Done

callKernel (Imp.LaunchKernel name args kernel_size workgroup_size) = do
  kernel_size' <- mapM Py.compileExp kernel_size
  let total_elements = foldl mult_exp (Constant $ value (1::Int32)) kernel_size'
  let cond = BinaryOp "!=" total_elements (Constant $ value (0::Int32))
  workgroup_size' <- Tuple <$> mapM (fmap asLong . Py.compileExp) workgroup_size
  body <- Py.collect $ launchKernel name kernel_size' workgroup_size' args
  Py.stm $ If cond body []
  return Py.Done
  where mult_exp = BinaryOp "*"

launchKernel :: String -> [PyExp] -> PyExp -> [Imp.KernelArg] -> Py.CompilerM op s ()
launchKernel kernel_name kernel_dims workgroup_dims args = do
  let kernel_dims' = Tuple $ map asLong kernel_dims
  let kernel_name' = "self." ++ kernel_name ++ "_var"
  args' <- mapM processKernelArg args
  Py.stm $ Exp $ Call (kernel_name' ++ ".set_args") $ map Arg args'
  Py.stm $ Exp $ Call "cl.enqueue_nd_range_kernel"
    [Arg $ Var "self.queue", Arg $ Var kernel_name',
     Arg kernel_dims', Arg workgroup_dims]
  finishIfSynchronous
  where processKernelArg :: Imp.KernelArg -> Py.CompilerM op s PyExp
        processKernelArg (Imp.ValueArg e bt) = do
          e' <- Py.compileExp e
          return $ Call (Py.compilePrimToNp bt) [Arg e']
        processKernelArg (Imp.MemArg v) = return $ Var $ pretty v
        processKernelArg (Imp.SharedMemoryArg (Imp.Count num_bytes)) = do
          num_bytes' <- Py.compileExp num_bytes
          return $ Call "cl.LocalMemory" [Arg $ asLong num_bytes']

writeOpenCLScalar :: Py.WriteScalar Imp.OpenCL ()
writeOpenCLScalar mem i bt "device" val = do
  let mem' = Var $ pretty mem
  let nparr = Call "np.array"
              [Arg val, ArgKeyword "dtype" $ Var $ Py.compilePrimType bt]
  Py.stm $ Exp $ Call "cl.enqueue_copy"
    [Arg $ Var "self.queue", Arg mem', Arg nparr,
     ArgKeyword "device_offset" $ asLong i,
     ArgKeyword "is_blocking" $ Var "synchronous"]

writeOpenCLScalar _ _ _ space _ =
  fail $ "Cannot write to '" ++ space ++ "' memory space."

readOpenCLScalar :: Py.ReadScalar Imp.OpenCL ()
readOpenCLScalar mem i bt "device" = do
  val <- newVName "read_res"
  let val' = Var $ pretty val
  let mem' = Var $ pretty mem
  let nparr = Call "np.empty" [Arg $ Constant $ value (1::Int32),
                               ArgKeyword "dtype" (Var $ Py.compilePrimType bt)]
  Py.stm $ Assign val' nparr
  Py.stm $ Exp $ Call "cl.enqueue_copy"
    [Arg $ Var "self.queue", Arg val', Arg mem',
     ArgKeyword "device_offset" $ asLong i,
     ArgKeyword "is_blocking" $ Constant $ BoolValue True]
  return $ Index val' $ IdxExp $ Constant $ value (0::Int32)

readOpenCLScalar _ _ _ space =
  fail $ "Cannot read from '" ++ space ++ "' memory space."

allocateOpenCLBuffer :: Py.Allocate Imp.OpenCL ()
allocateOpenCLBuffer mem size "device" = do
  let cond' = Cond (BinaryOp ">" size (Constant $ value (0::Int32))) (asLong size) (Constant $ value (1::Int32))
  let call' = Call "cl.Buffer" [Arg $ Var "self.ctx",
                                Arg $ Var "cl.mem_flags.READ_WRITE",
                                Arg $ asLong cond']
  Py.stm $ Assign (Var $ pretty mem) call'

allocateOpenCLBuffer _ _ space =
  fail $ "Cannot allocate in '" ++ space ++ "' space"

copyOpenCLMemory :: Py.Copy Imp.OpenCL ()
copyOpenCLMemory destmem destidx Imp.DefaultSpace srcmem srcidx (Imp.Space "device") nbytes bt = do
  let srcmem'  = Var $ pretty srcmem
  let destmem' = Var $ pretty destmem
  let divide = BinaryOp "//" nbytes (Var $ Py.compileSizeOfType bt)
  let end = BinaryOp "+" destidx divide
  let dest = Index destmem' (IdxRange destidx end)
  Py.stm $ ifNotZeroSize nbytes $
    Exp $ Call "cl.enqueue_copy"
    [Arg $ Var "self.queue", Arg dest, Arg srcmem',
     ArgKeyword "device_offset" $ asLong srcidx,
     ArgKeyword "is_blocking" $ Var "synchronous"]

copyOpenCLMemory destmem destidx (Imp.Space "device") srcmem srcidx Imp.DefaultSpace nbytes bt = do
  let destmem' = Var $ pretty destmem
  let srcmem'  = Var $ pretty srcmem
  let divide = BinaryOp "//" nbytes (Var $ Py.compileSizeOfType bt)
  let end = BinaryOp "+" srcidx divide
  let src = Index srcmem' (IdxRange srcidx end)
  Py.stm $ ifNotZeroSize nbytes $
    Exp $ Call "cl.enqueue_copy"
    [Arg $ Var "self.queue", Arg destmem', Arg src,
     ArgKeyword "device_offset" $ asLong destidx,
     ArgKeyword "is_blocking" $ Var "synchronous"]

copyOpenCLMemory destmem destidx (Imp.Space "device") srcmem srcidx (Imp.Space "device") nbytes _ = do
  let destmem' = Var $ pretty destmem
  let srcmem'  = Var $ pretty srcmem
  Py.stm $ ifNotZeroSize nbytes $
    Exp $ Call "cl.enqueue_copy"
    [Arg $ Var "self.queue", Arg destmem', Arg srcmem',
     ArgKeyword "dest_offset" $ asLong destidx,
     ArgKeyword "src_offset" $ asLong srcidx,
     ArgKeyword "byte_count" $ asLong nbytes]
  finishIfSynchronous

copyOpenCLMemory _ _ destspace _ _ srcspace _ _=
  error $ "Cannot copy to " ++ show destspace ++ " from " ++ show srcspace

ifNotZeroSize :: PyExp -> PyStmt -> PyStmt
ifNotZeroSize e s =
  If (BinaryOp "!=" e (Constant $ value (0::Int32))) [s] []

finishIfSynchronous :: Py.CompilerM op s ()
finishIfSynchronous =
  Py.stm $ If (Var "synchronous") [Exp $ Call "self.queue.finish" []] []
