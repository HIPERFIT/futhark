-- | Sequential imperative code.
module Futhark.CodeGen.ImpCode.Sequential
       ( Program
       , Function
       , FunctionT (Function)
       , Code
       , Sequential
       , module Futhark.CodeGen.ImpCode
       )
       where

import Futhark.CodeGen.ImpCode hiding (Function, Code)
import qualified Futhark.CodeGen.ImpCode as Imp

import Futhark.Util.Pretty hiding (space)

-- | An imperative program.
type Program = Imp.Functions Sequential

-- | An imperative function.
type Function = Imp.Function Sequential

-- | A piece of imperative code.
type Code = Imp.Code Sequential

-- | Phantom type for identifying sequential imperative code.
data Sequential

instance Pretty Sequential where
  ppr _ = empty
