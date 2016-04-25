{-# LANGUAGE QuasiQuotes, OverloadedStrings #-}
module Futhark.CodeGen.Backends.PyOpenCL.Boilerplate
  ( openClInit
  ) where

import qualified Data.Text as T
import NeatInterpolation (text)

import Futhark.Representation.AST.Attributes.Constants (value)
import Futhark.CodeGen.OpenCL.Kernels
import Futhark.CodeGen.Backends.GenericPython.AST
import Futhark.Util.Pretty (pretty)

openClInit :: String -> String
openClInit assign = T.unpack [text|
self.ctx = cl.create_some_context(interactive=False)
self.queue = cl.CommandQueue(self.ctx)
 # XXX: Assuming just a single device here.
platform_name = self.ctx.get_info(cl.context_info.DEVICES)[0].platform.name
device_type = self.ctx.get_info(cl.context_info.DEVICES)[0].type
lockstep_width = 1
$set_lockstep_width
if (len(fut_opencl_src) >= 0):
  program = cl.Program(self.ctx, fut_opencl_src).build(["-DFUT_BLOCK_DIM={}".format(FUT_BLOCK_DIM), "-DLOCKSTEP_WIDTH={}".format(lockstep_width)])

$assign'
|]
  where assign' = T.pack assign
        set_lockstep_width =
          T.pack $ unlines $
          map (pretty . lockstepWidthHeuristicsCode) lockstepWidthHeuristicsTable


lockstepWidthHeuristicsCode :: LockstepWidthHeuristic -> PyStmt
lockstepWidthHeuristicsCode
  (LockstepWidthHeuristic platform_name device_type width) =
  If (BinOp "and"
      (BinOp "==" (Var "platform_name") (StringLiteral platform_name))
      (BinOp "==" (Var "device_type") (clDeviceType device_type)))
  [Assign (Var "lockstep_width") (Constant (value (fromIntegral width::Int32)))]
  []
  where clDeviceType DeviceGPU = Var "cl.device_type.GPU"
        clDeviceType DeviceCPU = Var "cl.device_type.CPU"
