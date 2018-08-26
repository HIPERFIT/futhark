{-# LANGUAGE OverloadedStrings #-}
-- | Types (and a few other simple definitions) for futhark-pkg.
module Futhark.Pkg.Types
  ( PkgPath
  , pkgPathFilePath
  , PkgRevDeps(..)
  , module Data.Versions

  -- * Versions
  , commitVersion
  , isCommitVersion
  , parseVersion

  -- * Package manifests
  , PkgManifest(..)
  , newPkgManifest
  , pkgRevDeps
  , pkgDir
  , addRequiredToManifest
  , removeRequiredFromManifest
  , prettyPkgManifest
  , Comment
  , Commented(..)
  , Required(..)
  , futharkPkg

  -- * Parsing package manifests
  , parsePkgManifest
  , parsePkgManifestFromFile
  , parseErrorPretty

  -- * Build list
  , BuildList(..)
  , prettyBuildList
  ) where

import Control.Applicative
import Control.Monad
import Data.Either
import Data.Foldable
import Data.List
import Data.Maybe
import Data.Traversable
import Data.Ord (comparing)
import Data.Void
import Data.Semigroup ((<>))
import qualified Data.Semigroup as Sem
import qualified Data.Text as T
import qualified Data.Text.IO as T
import qualified Data.Map as M
import System.FilePath
import qualified System.FilePath.Posix as Posix

import Data.Versions (SemVer(..), VUnit(..), prettySemVer)
import Text.Megaparsec hiding (many, some)
import Text.Megaparsec.Char
import Text.Megaparsec.Error (parseErrorPretty)

import Prelude

-- | A package path is a unique identifier for a package, for example
-- @github.com/user/foo@.
type PkgPath = T.Text

-- | Turn a package path (which always uses forward slashes) into a
-- file path in the local file system (which might use different
-- slashes).
pkgPathFilePath :: PkgPath -> FilePath
pkgPathFilePath = joinPath . Posix.splitPath . T.unpack

-- | Versions of the form (0,0,0)-timestamp+hash are treated
-- specially, as a reference to the commit identified uniquely with
-- 'hash' (typically the Git commit ID).  This function detects such
-- versions.
isCommitVersion :: SemVer -> Maybe T.Text
isCommitVersion (SemVer 0 0 0 [_] [[Str s]]) = Just s
isCommitVersion _ = Nothing

-- | @commitVersion timestamp commit@ constructs a commit version.
commitVersion :: T.Text -> T.Text -> SemVer
commitVersion time commit =
  SemVer 0 0 0 [[Str time]] [[Str commit]]

-- | Unfortunately, Data.Versions has a buggy semver parser that
-- collapses consecutive zeroes in the metadata field.  So, we define
-- our own parser here.  It's a little simpler too, since we don't
-- need full semver.
parseVersion :: T.Text -> Either (ParseError (Token T.Text) Void) SemVer
parseVersion = parse (semver' <* eof) "Semantic Version"

semver' :: Parsec Void T.Text SemVer
semver' = SemVer <$> majorP <*> minorP <*> patchP <*> preRel <*> metaData
  where majorP = digitsP <* char '.'
        minorP = majorP
        patchP = digitsP
        digitsP = read <$> ((T.unpack <$> string "0") <|> some digitChar)
        preRel = maybe [] pure <$> optional preRel'
        preRel' = char '-' *> (pure . Str . T.pack <$> some digitChar)
        metaData = maybe [] pure <$> optional metaData'
        metaData' = char '+' *> (pure . Str . T.pack <$> some alphaNumChar)

-- | The dependencies of a (revision of a) package is a mapping from
-- package paths to minimum versions (and an optional hash pinning).
newtype PkgRevDeps = PkgRevDeps (M.Map PkgPath (SemVer, Maybe T.Text))
  deriving (Show)

instance Sem.Semigroup PkgRevDeps where
  PkgRevDeps x <> PkgRevDeps y = PkgRevDeps $ x <> y

instance Monoid PkgRevDeps where
  mempty = PkgRevDeps mempty
  mappend = (Sem.<>)

--- Package manifest

-- | A line comment.
type Comment = T.Text

-- | Wraps a value with an annotation of preceding line comments.
-- This is important to our goal of being able to programmatically
-- modify the @futhark.pkg@ file while keeping comments intact.
data Commented a = Commented { comments :: [Comment]
                             , commented :: a
                             }
                   deriving (Show, Eq)

instance Functor Commented where
  fmap = fmapDefault

instance Foldable Commented where
  foldMap = foldMapDefault

instance Traversable Commented where
  traverse f (Commented cs x) = Commented cs <$> f x

-- | An entry in the @required@ section of a @futhark.pkg@ file.
data Required = Required
                { requiredPkg :: PkgPath
                  -- ^ Name of the required package.
                , requiredPkgRev :: SemVer
                  -- ^ The minimum revision.
                , requiredHash :: Maybe T.Text
                  -- ^ An optional hash indicating what
                  -- this revision looked like the last
                  -- time we saw it.  Used for integrity
                  -- checking.
                }
                deriving (Show, Eq)

-- | The name of the file containing the futhark-pkg manifest.
futharkPkg :: FilePath
futharkPkg = "futhark.pkg"

-- | A structure corresponding to a @futhark.pkg@ file, including
-- comments.  It is an invariant that duplicate required packages do
-- not occcur (the parser will verify this).
data PkgManifest = PkgManifest { manifestPkgPath :: Commented (Maybe PkgPath)
                               -- ^ The name of the package.
                               , manifestRequire :: Commented [Either Comment Required]
                               , manifestEndComments :: [Comment]
                               }
                   deriving (Show, Eq)

-- | Possibly given a package path, construct an otherwise-empty manifest file.
newPkgManifest :: Maybe PkgPath -> PkgManifest
newPkgManifest p =
  PkgManifest (Commented mempty p) (Commented mempty mempty) mempty

-- | Prettyprint a package manifest such that it can be written to a
-- @futhark.pkg@ file.
prettyPkgManifest :: PkgManifest -> T.Text
prettyPkgManifest (PkgManifest name required endcs) =
  T.unlines $ concat [ prettyComments name
                     , maybe [] (pure . ("package "<>) . (<>"\n")) $ commented name
                     , prettyComments required
                     , ["require {"]
                     , map (("  "<>) . prettyRequired) $ commented required
                     , ["}"]
                     , map prettyComment endcs
                     ]
  where prettyComments = map prettyComment . comments
        prettyComment = ("--"<>)
        prettyRequired (Left c) = prettyComment c
        prettyRequired (Right (Required p r h)) =
          T.unwords $ catMaybes [Just p,
                                 Just $ prettySemVer r,
                                 ("#"<>) <$> h]

-- | The required packages listed in a package manifest.
pkgRevDeps :: PkgManifest -> PkgRevDeps
pkgRevDeps = PkgRevDeps . M.fromList . mapMaybe onR .
             commented .  manifestRequire
  where onR (Right r) = Just (requiredPkg r, (requiredPkgRev r, requiredHash r))
        onR (Left _) = Nothing

-- | Where in the corresponding repository archive we can expect to
-- find the package files.
pkgDir :: PkgManifest -> Maybe Posix.FilePath
pkgDir = fmap (Posix.addTrailingPathSeparator . ("lib" Posix.</>) .
               T.unpack) . commented . manifestPkgPath

-- | Add new required package to the package manifest.  If the package
-- was already present, return the old version.
addRequiredToManifest :: Required -> PkgManifest -> (PkgManifest, Maybe Required)
addRequiredToManifest new_r pm =
  let (old, requires') = mapAccumL add Nothing $ commented $ manifestRequire pm
  in (if isJust old
      then pm { manifestRequire = const requires' <$> manifestRequire pm }
      else pm { manifestRequire = (++[Right new_r]) <$> manifestRequire pm },
      old)
  where add acc (Left c) = (acc, Left c)
        add acc (Right r)
          | requiredPkg r == requiredPkg new_r = (Just r, Right new_r)
          | otherwise                          = (acc, Right r)

-- | Check if the manifest specifies a required package with the given
-- package path.
requiredInManifest :: PkgPath -> PkgManifest -> Maybe Required
requiredInManifest p =
  find ((==p) . requiredPkg) . rights . commented . manifestRequire

-- | Remove a required package from the manifest.  Returns 'Nothing'
-- if the package was not found in the manifest, and otherwise the new
-- manifest and the 'Required' that was present.
removeRequiredFromManifest :: PkgPath -> PkgManifest -> Maybe (PkgManifest, Required)
removeRequiredFromManifest p pm = do
  r <- requiredInManifest p pm
  return (pm { manifestRequire = filter (not . matches) <$> manifestRequire pm },
          r)
  where matches = either (const False) ((==p) . requiredPkg)

--- Parsing futhark.pkg.

type Parser = Parsec Void T.Text

pPkgManifest :: Parser PkgManifest
pPkgManifest = do
  c1 <- pComments
  p <- optional $ lexstr "package" *> pPkgPath
  space
  c2 <- pComments
  required <- (lexstr "require" *>
               braces (many $ (Left <$> pComment) <|> (Right <$> pRequired)))
              <|> pure []
  c3 <- pComments
  eof
  return $ PkgManifest (Commented c1 p) (Commented c2 required) c3
  where lexeme :: Parser a -> Parser a
        lexeme p = p <* space

        lexeme' p = p <* spaceNoEol

        lexstr :: T.Text -> Parser ()
        lexstr = void . try . lexeme . string

        braces :: Parser a -> Parser a
        braces p = lexstr "{" *> p <* lexstr "}"

        spaceNoEol = many $ oneOf (" \t" :: String)

        pPkgPath = T.pack <$> some (alphaNumChar <|> oneOf ("@-/.:" :: String))
                   <?> "package path"

        pRequired = space *> (Required <$> lexeme' pPkgPath
                                       <*> lexeme' semver'
                                       <*> optional (lexeme' pHash)) <* space
                    <?> "package requirement"

        pHash = char '#' *> (T.pack <$> some alphaNumChar)

        pComment = lexeme $ T.pack <$> (string "--" >> anyChar `manyTill` (void eol <|> eof))

        pComments :: Parser [Comment]
        pComments = catMaybes <$> many (comment <|> blankLine)
          where comment = Just <$> pComment
                blankLine = some spaceChar >> pure Nothing


parsePkgManifest :: FilePath -> T.Text -> Either (ParseError Char Void) PkgManifest
parsePkgManifest = parse pPkgManifest

parsePkgManifestFromFile :: FilePath -> IO PkgManifest
parsePkgManifestFromFile f = do
  s <- T.readFile f
  case parsePkgManifest f s of
    Left err -> fail $ parseErrorPretty err
    Right m -> return m

-- | A mapping from package paths to their chosen revisions.  This is
-- the result of the version solver.
newtype BuildList = BuildList { unBuildList :: M.Map PkgPath SemVer }
                  deriving (Eq, Show)

-- | Prettyprint a build list; one package per line and
-- newline-terminated.
prettyBuildList :: BuildList -> T.Text
prettyBuildList (BuildList m) = T.unlines $ map f $ sortBy (comparing fst) $ M.toList m
  where f (p, v) = T.unwords [p, "=>", prettySemVer v]
