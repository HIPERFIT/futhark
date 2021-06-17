-- | Definitions of various semantic objects (*not* the Futhark
-- semantics themselves).
module Language.Futhark.Semantic
  ( ImportName,
    mkInitialImport,
    mkImportFrom,
    includeToFilePath,
    includeToString,
    FileModule (..),
    Imports,
    Namespace (..),
    Env (..),
    TySet,
    FunSig (..),
    NameMap,
    BoundV (..),
    Mod (..),
    TypeBinding (..),
    MTy (..),
  )
where

import qualified Data.Map.Strict as M
import Futhark.Util (dropLast, fromPOSIX, toPOSIX)
import Futhark.Util.Loc
import Futhark.Util.Pretty
import Language.Futhark
import qualified System.FilePath as Native
import qualified System.FilePath.Posix as Posix
import Prelude hiding (mod)

-- | Canonical reference to a Futhark code file.  Does not include the
-- @.fut@ extension.  This is most often a path relative to the
-- current working directory of the compiler.
data ImportName = ImportName Posix.FilePath SrcLoc
  deriving (Eq, Ord, Show)

instance Located ImportName where
  locOf (ImportName _ loc) = locOf loc

-- | Create an import name immediately from a file path specified by
-- the user.
mkInitialImport :: Native.FilePath -> ImportName
mkInitialImport s = ImportName (Posix.normalise $ toPOSIX s) noLoc

-- | We resolve '..' paths here and assume that no shenanigans are
-- going on with symbolic links.  If there is, too bad.  Don't do
-- that.
mkImportFrom :: ImportName -> String -> SrcLoc -> ImportName
mkImportFrom (ImportName includer _) includee
  | Posix.isAbsolute includee = ImportName includee
  | otherwise = ImportName $ Posix.normalise $ Posix.joinPath $ includer' ++ includee'
  where
    (dotdots, includee') = span ("../" ==) $ Posix.splitPath includee
    includer_parts = init $ Posix.splitPath includer
    includer'
      | length dotdots > length includer_parts =
        replicate (length dotdots - length includer_parts) "../"
      | otherwise =
        dropLast (length dotdots) includer_parts

-- | Create a @.fut@ file corresponding to an 'ImportName'.
includeToFilePath :: ImportName -> Native.FilePath
includeToFilePath (ImportName s _) = fromPOSIX $ Posix.normalise s Posix.<.> "fut"

-- | Produce a human-readable canonicalized string from an
-- 'ImportName'.
includeToString :: ImportName -> String
includeToString (ImportName s _) = Posix.normalise $ Posix.makeRelative "/" s

-- | The result of type checking some file.  Can be passed to further
-- invocations of the type checker.
data FileModule = FileModule
  { -- | Abstract types.
    fileAbs :: TySet,
    fileEnv :: Env,
    fileProg :: Prog
  }

-- | A mapping from import names to imports.  The ordering is significant.
type Imports = [(String, FileModule)]

-- | The space inhabited by a name.
data Namespace
  = -- | Functions and values.
    Term
  | Type
  | Signature
  deriving (Eq, Ord, Show, Enum)

-- | A mapping of abstract types to their liftedness.
type TySet = M.Map (QualName VName) Liftedness

-- | Representation of a module, which is either a plain environment,
-- or a parametric module ("functor" in SML).
data Mod
  = ModEnv Env
  | ModFun FunSig
  deriving (Show)

-- | A parametric functor consists of a set of abstract types, the
-- environment of its parameter, and the resulting module type.
data FunSig = FunSig
  { funSigAbs :: TySet,
    funSigMod :: Mod,
    funSigMty :: MTy
  }
  deriving (Show)

-- | Representation of a module type.
data MTy = MTy
  { -- | Abstract types in the module type.
    mtyAbs :: TySet,
    mtyMod :: Mod
  }
  deriving (Show)

-- | A binding from a name to its definition as a type.  We allow a
-- return type here to support type abbreviations that hide some inner
-- sizes (these must necessarily be 'Lifted' or 'SizeLifted').
data TypeBinding = TypeAbbr Liftedness [TypeParam] StructRetType
  deriving (Eq, Show)

-- | Type parameters, list of parameter types (optinally named), and
-- return type.  The type parameters are in scope in both parameter
-- types and the return type.  Non-functional values have only a
-- return type.
data BoundV = BoundV [TypeParam] StructType
  deriving (Show)

-- | A mapping from names (which always exist in some namespace) to a
-- unique (tagged) name.
type NameMap = M.Map (Namespace, Name) (QualName VName)

-- | Modules produces environment with this representation.
data Env = Env
  { envVtable :: M.Map VName BoundV,
    envTypeTable :: M.Map VName TypeBinding,
    envSigTable :: M.Map VName MTy,
    envModTable :: M.Map VName Mod,
    envNameMap :: NameMap
  }
  deriving (Show)

instance Semigroup Env where
  Env vt1 tt1 st1 mt1 nt1 <> Env vt2 tt2 st2 mt2 nt2 =
    Env (vt1 <> vt2) (tt1 <> tt2) (st1 <> st2) (mt1 <> mt2) (nt1 <> nt2)

instance Pretty Namespace where
  ppr Term = text "name"
  ppr Type = text "type"
  ppr Signature = text "module type"

instance Monoid Env where
  mempty = Env mempty mempty mempty mempty mempty

instance Pretty MTy where
  ppr = ppr . mtyMod

instance Pretty Mod where
  ppr (ModEnv e) = ppr e
  ppr (ModFun (FunSig _ mod mty)) = ppr mod <+> text "->" </> ppr mty

instance Pretty Env where
  ppr (Env vtable ttable sigtable modtable _) =
    nestedBlock "{" "}" $
      stack $
        punctuate line $
          concat
            [ map renderTypeBind (M.toList ttable),
              map renderValBind (M.toList vtable),
              map renderModType (M.toList sigtable),
              map renderMod (M.toList modtable)
            ]
    where
      renderTypeBind (name, TypeAbbr l tps tp) =
        p l <+> pprName name <> mconcat (map ((text " " <>) . ppr) tps)
          <> text " =" <+> ppr tp
        where
          p Lifted = text "type^"
          p SizeLifted = text "type~"
          p Unlifted = text "type"
      renderValBind (name, BoundV tps t) =
        text "val" <+> pprName name <> mconcat (map ((text " " <>) . ppr) tps)
          <> text " =" <+> ppr t
      renderModType (name, _sig) =
        text "module type" <+> pprName name
      renderMod (name, mod) =
        text "module" <+> pprName name <> text " =" <+> ppr mod
