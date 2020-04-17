{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
-- | Variation of "Futhark.CodeGen.ImpCode" that contains the notion
-- of a kernel invocation.
module Futhark.CodeGen.ImpCode.Kernels
  ( Program
  , Function
  , FunctionT (Function)
  , Code
  , KernelCode
  , KernelConst (..)
  , KernelConstExp
  , HostOp (..)
  , KernelOp (..)
  , Fence (..)
  , AtomicOp (..)
  , Kernel (..)
  , KernelUse (..)
  , module Futhark.CodeGen.ImpCode
  , module Futhark.Representation.Kernels.Sizes
  -- * Utility functions
  , atomicBinOp
  )
  where

import Futhark.CodeGen.ImpCode hiding (Function, Code)
import qualified Futhark.CodeGen.ImpCode as Imp
import Futhark.Representation.Kernels.Sizes
import Futhark.Representation.AST.Attributes.Names
import Futhark.Representation.AST.Pretty ()
import Futhark.Util.Pretty

type Program = Imp.Definitions HostOp
type Function = Imp.Function HostOp
-- | Host-level code that can call kernels.
type Code = Imp.Code HostOp
-- | Code inside a kernel.
type KernelCode = Imp.Code KernelOp

-- | A run-time constant related to kernels.
newtype KernelConst = SizeConst Name
                    deriving (Eq, Ord, Show)

-- | An expression whose variables are kernel constants.
type KernelConstExp = PrimExp KernelConst

data HostOp = CallKernel Kernel
            | GetSize VName Name SizeClass
            | CmpSizeLe VName Name SizeClass Imp.Exp
            | GetSizeMax VName SizeClass
            deriving (Show)

-- | A generic kernel containing arbitrary kernel code.
data Kernel = Kernel
              { kernelBody :: Imp.Code KernelOp

              , kernelUses :: [KernelUse]
                -- ^ The host variables referenced by the kernel.

              , kernelNumGroups :: [Imp.Exp]
              , kernelGroupSize :: [Imp.Exp]
              , kernelName :: Name
               -- ^ A short descriptive and _unique_ name - should be
               -- alphanumeric and without spaces.

              , kernelFailureTolerant :: Bool
                -- ^ If true, this kernel does not need for check
                -- whether we are in a failing state, as it can cope.
                -- Intuitively, it means that the kernel does not
                -- depend on any non-scalar parameters to make control
                -- flow decisions.  Replication, transpose, and copy
                -- kernels are examples of this.
              }
            deriving (Show)

data KernelUse = ScalarUse VName PrimType
               | MemoryUse VName
               | ConstUse VName KernelConstExp
                 deriving (Eq, Show)

-- | Get an atomic operator corresponding to a binary operator.
atomicBinOp :: BinOp -> Maybe (VName -> VName -> Count Elements Imp.Exp -> Exp -> AtomicOp)
atomicBinOp = flip lookup [ (Add Int32, AtomicAdd Int32)
                          , (FAdd Float32, AtomicFAdd Float32)
                          , (SMax Int32, AtomicSMax Int32)
                          , (SMin Int32, AtomicSMin Int32)
                          , (UMax Int32, AtomicUMax Int32)
                          , (UMin Int32, AtomicUMin Int32)
                          , (And Int32, AtomicAnd Int32)
                          , (Or Int32, AtomicOr Int32)
                          , (Xor Int32, AtomicXor Int32)
                          ]

instance Pretty KernelConst where
  ppr (SizeConst key) = text "get_size" <> parens (ppr key)

instance Pretty KernelUse where
  ppr (ScalarUse name t) =
    oneLine $ text "scalar_copy" <> parens (commasep [ppr name, ppr t])
  ppr (MemoryUse name) =
    oneLine $ text "mem_copy" <> parens (commasep [ppr name])
  ppr (ConstUse name e) =
    oneLine $ text "const" <> parens (commasep [ppr name, ppr e])

instance Pretty HostOp where
  ppr (GetSize dest key size_class) =
    ppr dest <+> text "<-" <+>
    text "get_size" <> parens (commasep [ppr key, ppr size_class])
  ppr (GetSizeMax dest size_class) =
    ppr dest <+> text "<-" <+> text "get_size_max" <> parens (ppr size_class)
  ppr (CmpSizeLe dest name size_class x) =
    ppr dest <+> text "<-" <+>
    text "get_size" <> parens (commasep [ppr name, ppr size_class]) <+>
    text "<" <+> ppr x
  ppr (CallKernel c) =
    ppr c

instance FreeIn HostOp where
  freeIn' (CallKernel c) =
    freeIn' c
  freeIn' (CmpSizeLe dest _ _ x) =
    freeIn' dest <> freeIn' x
  freeIn' (GetSizeMax dest _) =
    freeIn' dest
  freeIn' (GetSize dest _ _) =
    freeIn' dest

instance FreeIn Kernel where
  freeIn' kernel = freeIn' (kernelBody kernel) <>
                   freeIn' [kernelNumGroups kernel, kernelGroupSize kernel]

instance Pretty Kernel where
  ppr kernel =
    text "kernel" <+> brace
    (text "groups" <+> brace (ppr $ kernelNumGroups kernel) </>
     text "group_size" <+> brace (ppr $ kernelGroupSize kernel) </>
     text "uses" <+> brace (commasep $ map ppr $ kernelUses kernel) </>
     text "failure_tolerant" <+> ppr (kernelFailureTolerant kernel) </>
     text "body" <+> brace (ppr $ kernelBody kernel))

-- | When we do a barrier or fence, is it at the local or global
-- level?
data Fence = FenceLocal | FenceGlobal
           deriving (Show)

data KernelOp = GetGroupId VName Int
              | GetLocalId VName Int
              | GetLocalSize VName Int
              | GetGlobalSize VName Int
              | GetGlobalId VName Int
              | GetLockstepWidth VName
              | Atomic Space AtomicOp
              | Barrier Fence
              | MemFence Fence
              | LocalAlloc VName (Count Bytes Imp.Exp)
              | ErrorSync Fence
                -- ^ Perform a barrier and also check whether any
                -- threads have failed an assertion.  Make sure all
                -- threads would reach all 'ErrorSync's if any of them
                -- do.  A failing assertion will jump to the next
                -- following 'ErrorSync', so make sure it's not inside
                -- control flow or similar.
              deriving (Show)

-- Atomic operations return the value stored before the update.
-- This value is stored in the first VName.
data AtomicOp = AtomicAdd IntType VName VName (Count Elements Imp.Exp) Exp
              | AtomicFAdd FloatType VName VName (Count Elements Imp.Exp) Exp
              | AtomicSMax IntType VName VName (Count Elements Imp.Exp) Exp
              | AtomicSMin IntType VName VName (Count Elements Imp.Exp) Exp
              | AtomicUMax IntType VName VName (Count Elements Imp.Exp) Exp
              | AtomicUMin IntType VName VName (Count Elements Imp.Exp) Exp
              | AtomicAnd IntType VName VName (Count Elements Imp.Exp) Exp
              | AtomicOr IntType VName VName (Count Elements Imp.Exp) Exp
              | AtomicXor IntType VName VName (Count Elements Imp.Exp) Exp
              | AtomicCmpXchg PrimType VName VName (Count Elements Imp.Exp) Exp Exp
              | AtomicXchg PrimType VName VName (Count Elements Imp.Exp) Exp
              deriving (Show)

instance FreeIn AtomicOp where
  freeIn' (AtomicAdd _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicFAdd _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicSMax _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicSMin _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicUMax _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicUMin _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicAnd _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicOr _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicXor _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x
  freeIn' (AtomicCmpXchg _ _ arr i x y) = freeIn' arr <> freeIn' i <> freeIn' x <> freeIn' y
  freeIn' (AtomicXchg _ _ arr i x) = freeIn' arr <> freeIn' i <> freeIn' x

instance Pretty KernelOp where
  ppr (GetGroupId dest i) =
    ppr dest <+>  "<-" <+>
     "get_group_id" <> parens (ppr i)
  ppr (GetLocalId dest i) =
    ppr dest <+>  "<-" <+>
     "get_local_id" <> parens (ppr i)
  ppr (GetLocalSize dest i) =
    ppr dest <+>  "<-" <+>
     "get_local_size" <> parens (ppr i)
  ppr (GetGlobalSize dest i) =
    ppr dest <+>  "<-" <+>
     "get_global_size" <> parens (ppr i)
  ppr (GetGlobalId dest i) =
    ppr dest <+>  "<-" <+>
     "get_global_id" <> parens (ppr i)
  ppr (GetLockstepWidth dest) =
    ppr dest <+>  "<-" <+>
     "get_lockstep_width()"
  ppr (Barrier FenceLocal) =
     "local_barrier()"
  ppr (Barrier FenceGlobal) =
     "global_barrier()"
  ppr (MemFence FenceLocal) =
     "mem_fence_local()"
  ppr (MemFence FenceGlobal) =
     "mem_fence_global()"
  ppr (LocalAlloc name size) =
    ppr name <+> equals <+>  "local_alloc" <> parens (ppr size)
  ppr (ErrorSync FenceLocal) =
     "error_sync_local()"
  ppr (ErrorSync FenceGlobal) =
     "error_sync_global()"
  ppr (Atomic _ (AtomicAdd t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_add_" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicFAdd t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_fadd_" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicSMax t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_smax" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicSMin t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_smin" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicUMax t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_umax" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicUMin t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_umin" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicAnd t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_and" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicOr t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_or" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicXor t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_xor" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])
  ppr (Atomic _ (AtomicCmpXchg t old arr ind x y)) =
    ppr old <+>  "<-" <+>  "atomic_cmp_xchg" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x, ppr y])
  ppr (Atomic _ (AtomicXchg t old arr ind x)) =
    ppr old <+>  "<-" <+>  "atomic_xchg" <> ppr t <>
    parens (commasep [ppr arr <> brackets (ppr ind), ppr x])

instance FreeIn KernelOp where
  freeIn' (Atomic _ op) = freeIn' op
  freeIn' _ = mempty

brace :: Doc -> Doc
brace body =  " {" </> indent 2 body </>  "}"
