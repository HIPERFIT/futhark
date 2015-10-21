-- | Imperative code with an OpenCL component.
--
-- Apart from ordinary imperative code, this also carries around an
-- OpenCL program as a string, as well as a list of kernels defined by
-- the OpenCL program.
--
-- The imperative code has been augmented with a 'LaunchKernel'
-- operation that allows one to execute an OpenCL kernel.
module Futhark.CodeGen.ImpCode.OpenCL
       ( Program (..)
       , Function
       , FunctionT (Function)
       , Code
       , KernelName
       , KernelArg (..)
       , OpenCL (..)
       , transposeBlockDim
       , module Futhark.CodeGen.ImpCode
       )
       where

import Futhark.CodeGen.ImpCode hiding (Function, Code)
import qualified Futhark.CodeGen.ImpCode as Imp

import Futhark.Util.Pretty hiding (space)

-- | An program calling OpenCL kernels.
data Program = Program { openClProgram :: String
                       , openClKernelNames :: [KernelName]
                       , hostFunctions :: Functions OpenCL
                       }

-- | A function calling OpenCL kernels.
type Function = Imp.Function OpenCL

-- | A piece of code calling OpenCL.
type Code = Imp.Code OpenCL

-- | The name of a kernel.
type KernelName = String

-- | An argument to be passed to a kernel.
data KernelArg = ValueArg Exp BasicType
                 -- ^ Pass the value of this scalar expression as argument.
               | MemArg VName
                 -- ^ Pass this pointer as argument.
               | SharedMemoryArg (Count Bytes)
                 -- ^ Create this much local memory per workgroup.
               deriving (Show)

-- | Host-level OpenCL operation.
data OpenCL = LaunchKernel KernelName [KernelArg] [Exp] (Maybe [Exp])
            deriving (Show)

-- | The block size when transposing.
transposeBlockDim :: Num a => a
transposeBlockDim = 16

instance Pretty OpenCL where
  ppr = text . show
