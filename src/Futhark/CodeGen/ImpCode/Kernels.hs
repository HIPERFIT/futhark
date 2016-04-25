{-# LANGUAGE FlexibleContexts #-}
-- | Variation of "Futhark.CodeGen.ImpCode" that contains the notion
-- of a kernel invocation.
module Futhark.CodeGen.ImpCode.Kernels
  ( Program
  , Function
  , FunctionT (Function)
  , Code
  , KernelCode
  , HostOp (..)
  , KernelOp (..)
  , CallKernel (..)
  , MapKernel (..)
  , Kernel (..)
  , KernelUse (..)
  , module Futhark.CodeGen.ImpCode
  -- * Utility functions
  , getKernels
  )
  where

import Control.Monad.Writer
import Data.List
import qualified Data.HashSet as HS
import Data.Traversable

import Prelude

import Futhark.CodeGen.ImpCode hiding (Function, Code)
import qualified Futhark.CodeGen.ImpCode as Imp
import Futhark.Representation.AST.Attributes.Names
import Futhark.Representation.AST.Pretty ()
import Futhark.Util.Pretty

type Program = Functions HostOp
type Function = Imp.Function HostOp
-- | Host-level code that can call kernels.
type Code = Imp.Code CallKernel
-- | Code inside a kernel.
type KernelCode = Imp.Code KernelOp

data HostOp = CallKernel CallKernel
            | GetNumGroups VName
            | GetGroupSize VName
            deriving (Show)

data CallKernel = Map MapKernel
                | AnyKernel Kernel
                | MapTranspose PrimType VName Exp VName Exp Exp Exp Exp Exp
            deriving (Show)

-- | A generic kernel containing arbitrary kernel code.
data MapKernel = MapKernel { mapKernelThreadNum :: VName
                             -- ^ Binding position - also serves as a unique
                             -- name for the kernel.
                           , mapKernelBody :: Imp.Code KernelOp
                           , mapKernelUses :: [KernelUse]
                           , mapKernelNumGroups :: DimSize
                           , mapKernelGroupSize :: DimSize
                           , mapKernelSize :: Imp.Exp
                           -- ^ Do not actually execute threads past this.
                           }
                     deriving (Show)

data Kernel = Kernel
              { kernelBody :: Imp.Code KernelOp
              , kernelLocalMemory :: [(VName, MemSize, PrimType)]
                -- ^ In-kernel name, per-workgroup size in bytes, and
                -- alignment restriction.

              , kernelUses :: [KernelUse]
                -- ^ The host variables referenced by the kernel.

              , kernelNumGroups :: DimSize
              , kernelGroupSize :: DimSize
              , kernelName :: VName
                -- ^ Unique name for the kernel.
              , kernelDesc :: Maybe String
               -- ^ An optional short descriptive name - should be
               -- alphanumeric and without spaces.
              }
            deriving (Show)

data KernelUse = ScalarUse VName PrimType
               | MemoryUse VName Imp.DimSize
                 deriving (Eq, Show)

getKernels :: Program -> [CallKernel]
getKernels = nubBy sameKernel . execWriter . traverse getFunKernels
  where getFunKernels (CallKernel kernel) =
          tell [kernel]
        getFunKernels _ =
          return ()
        sameKernel (MapTranspose bt1 _ _ _ _ _ _ _ _) (MapTranspose bt2 _ _ _ _ _ _ _ _) =
          bt1 == bt2
        sameKernel _ _ = False

instance Pretty KernelUse where
  ppr (ScalarUse name t) =
    text "scalar_copy" <> parens (commasep [ppr name, ppr t])
  ppr (MemoryUse name size) =
    text "mem_copy" <> parens (commasep [ppr name, ppr size])

instance Pretty HostOp where
  ppr (GetNumGroups dest) =
    ppr dest <+> text "<-" <+>
    text "get_num_groups()"
  ppr (GetGroupSize dest) =
    ppr dest <+> text "<-" <+>
    text "get_group_size()"
  ppr (CallKernel c) =
    ppr c

instance Pretty CallKernel where
  ppr (Map k) = ppr k
  ppr (AnyKernel k) = ppr k
  ppr (MapTranspose bt dest destoffset src srcoffset num_arrays size_x size_y total_elems) =
    text "mapTranspose" <>
    parens (ppr bt <> comma </>
            ppMemLoc dest destoffset <> comma </>
            ppMemLoc src srcoffset <> comma </>
            ppr num_arrays <> comma <+>
            ppr size_x <> comma <+>
            ppr size_y <> comma <+>
            ppr total_elems)
    where ppMemLoc base offset =
            ppr base <+> text "+" <+> ppr offset

instance Pretty MapKernel where
  ppr kernel =
    text "mapKernel" <+> brace
    (text "uses" <+> brace (commasep $ map ppr $ mapKernelUses kernel) </>
     text "body" <+> brace (ppr (mapKernelThreadNum kernel) <+>
                            text "<- get_thread_number()" </>
                            ppr (mapKernelBody kernel)))

instance Pretty Kernel where
  ppr kernel =
    text "kernel" <+> brace
    (text "groups" <+> brace (ppr $ kernelNumGroups kernel) </>
     text "group_size" <+> brace (ppr $ kernelGroupSize kernel) </>
     text "local_memory" <+> brace (commasep $
                                    map ppLocalMemory $
                                    kernelLocalMemory kernel) </>
     text "uses" <+> brace (commasep $ map ppr $ kernelUses kernel) </>
     text "body" <+> brace (ppr $ kernelBody kernel))
    where ppLocalMemory (name, size, bt) =
            ppr name <+> parens (ppr size <+> text "bytes" <> comma <+>
                                text "align to" <+> ppr bt)

instance FreeIn MapKernel where
  freeIn kernel =
    mapKernelThreadNum kernel `HS.delete` freeIn (mapKernelBody kernel)

data KernelOp = GetGroupId VName Int
              | GetLocalId VName Int
              | GetLocalSize VName Int
              | GetGlobalSize VName Int
              | GetGlobalId VName Int
              | GetLockstepWidth VName
              | Barrier
              deriving (Show)

instance Pretty KernelOp where
  ppr (GetGroupId dest i) =
    ppr dest <+> text "<-" <+>
    text "get_group_id" <> parens (ppr i)
  ppr (GetLocalId dest i) =
    ppr dest <+> text "<-" <+>
    text "get_local_id" <> parens (ppr i)
  ppr (GetLocalSize dest i) =
    ppr dest <+> text "<-" <+>
    text "get_local_size" <> parens (ppr i)
  ppr (GetGlobalSize dest i) =
    ppr dest <+> text "<-" <+>
    text "get_global_size" <> parens (ppr i)
  ppr (GetGlobalId dest i) =
    ppr dest <+> text "<-" <+>
    text "get_global_id" <> parens (ppr i)
  ppr (GetLockstepWidth dest) =
    ppr dest <+> text "<-" <+>
    text "get_lockstep_width()"
  ppr Barrier =
    text "barrier()"

instance FreeIn KernelOp where
  freeIn = const mempty

brace :: Doc -> Doc
brace body = text " {" </> indent 2 body </> text "}"
