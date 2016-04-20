-- | Facilities for reading Futhark test programs.  A Futhark test
-- program is an ordinary Futhark program where an initial comment
-- block specifies input- and output-sets.
module Futhark.Test
       ( testSpecFromFile
       , valuesFromText
       , getValues
       , getValuesText
       , compareValues
       , Mismatch

       , ProgramTest (..)
       , StructureTest (..)
       , StructurePipeline (..)
       , TestAction (..)
       , ExpectedError (..)
       , TestRun (..)
       , RunMode (..)
       , ExpectedResult (..)
       , Values (..)
       )
       where

import Control.Category ((>>>))
import Control.Applicative
import Control.Monad hiding (forM_)
import Control.Monad.IO.Class
import qualified Data.Array as A
import qualified Data.HashMap.Lazy as HM
import Data.Char
import Data.Maybe
import Data.Monoid
import Data.List hiding (foldl')
import Data.Foldable (foldl')
import qualified Data.Text as T
import qualified Data.Text.IO as T
import System.IO
import System.FilePath

import Text.Parsec hiding ((<|>), many, optional)
import Text.Parsec.Text
import Text.Parsec.Error
import Text.Regex.TDFA

import Prelude

import Futhark.Representation.AST.Attributes.Values (valueType)
import Futhark.Representation.AST.Syntax.Core hiding (Prim)
import Futhark.Internalise.TypesValues (internaliseValue)
import qualified Language.Futhark.Parser as F
import Futhark.Representation.SOACS (SOACS)
import Futhark.Representation.Kernels (Kernels)
import Futhark.Analysis.Metrics
import Futhark.Pipeline
import Futhark.Pass.Simplify
import Futhark.Pass.ExtractKernels
import Futhark.Passes
import Futhark.Util.Pretty (Pretty, pretty, prettyText)

-- | Description of a test to be carried out on a Futhark program.
-- The Futhark program is stored separately.
data ProgramTest =
  ProgramTest { testDescription ::
                   T.Text
              , testTags ::
                   [T.Text]
              , testAction ::
                   TestAction
              , testExpectedStructure ::
                   Maybe StructureTest
              }
  deriving (Show)

data TestAction
  = CompileTimeFailure ExpectedError
  | RunCases [TestRun]
  deriving (Show)

data ExpectedError = AnyError
                   | ThisError T.Text Regex

instance Show ExpectedError where
  show AnyError = "AnyError"
  show (ThisError r _) = "ThisError " ++ show r

data StructurePipeline = KernelsPipeline (Pipeline SOACS Kernels)
                       | SOACSPipeline (Pipeline SOACS SOACS)

data StructureTest = StructureTest StructurePipeline AstMetrics

instance Show StructureTest where
  show (StructureTest _ metrics) =
    "StructureTest <config> " ++ show metrics

data RunMode
  = CompiledOnly -- ^ Cannot run with interpreter.
  | InterpretedOnly -- ^ Only run with interpreter.
  | NoTravis -- ^ Requires a lot of memory, do not run in Travis.
  | InterpretedAndCompiled -- ^ Can be interpreted or compiled.
  deriving (Eq, Show)

data TestRun = TestRun
               { runMode :: RunMode
               , runInput :: Values
               , runExpectedResult :: ExpectedResult Values
               }
             deriving (Show)

data Values = Values [Value]
            | InFile FilePath
            deriving (Show)

data ExpectedResult values
  = Succeeds (Maybe values) -- ^ Execution suceeds, with or without
                            -- expected result values.
  | RunTimeFailure ExpectedError -- ^ Execution fails with this error.
  deriving (Show)

lexeme :: Parser a -> Parser a
lexeme p = p <* spaces

lexstr :: String -> Parser ()
lexstr = void . lexeme . string

braces :: Parser a -> Parser a
braces p = lexstr "{" *> p <* lexstr "}"

parseNatural :: Parser Int
parseNatural = lexeme $ foldl' (\acc x -> acc * 10 + x) 0 .
               map num <$> some digit
  where num c = ord c - ord '0'

parseDescription :: Parser T.Text
parseDescription = lexeme $ T.pack <$> (anyChar `manyTill` parseDescriptionSeparator)

parseDescriptionSeparator :: Parser ()
parseDescriptionSeparator = try (string descriptionSeparator >> void newline) <|> eof

descriptionSeparator :: String
descriptionSeparator = "=="

parseTags :: Parser [T.Text]
parseTags = lexstr "tags" *> braces (many parseTag) <|> pure []
  where parseTag = T.pack <$> lexeme (many1 $ satisfy constituent)
        constituent c = not (isSpace c) && c /= '}'

parseAction :: Parser TestAction
parseAction = CompileTimeFailure <$> (lexstr "error:" *> parseExpectedError) <|>
              RunCases <$> parseRunCases

parseRunMode :: Parser RunMode
parseRunMode = (lexstr "compiled" *> pure CompiledOnly) <|>
               (lexstr "notravis" *> pure NoTravis) <|>
               pure InterpretedAndCompiled

parseRunCases :: Parser [TestRun]
parseRunCases = many $ TestRun <$> parseRunMode <*> parseInput <*> parseExpectedResult

parseExpectedResult :: Parser (ExpectedResult Values)
parseExpectedResult =
  (Succeeds . Just <$> (lexstr "output" *> parseValues)) <|>
  (RunTimeFailure <$> (lexstr "error:" *> parseExpectedError)) <|>
  pure (Succeeds Nothing)

parseExpectedError :: Parser ExpectedError
parseExpectedError = lexeme $ do
  s <- restOfLine
  if T.all isSpace s
    then return AnyError
         -- blankCompOpt creates a regular expression that treats
         -- newlines like ordinary characters, which is what we want.
    else ThisError s <$> makeRegexOptsM blankCompOpt defaultExecOpt (T.unpack s)

parseInput :: Parser Values
parseInput = lexstr "input" *> parseValues

parseValues :: Parser Values
parseValues = do s <- parseBlock
                 case valuesFromText "input" s of
                   Left err -> fail $ show err
                   Right vs -> return $ Values vs
              <|> lexstr "@" *> lexeme (InFile . T.unpack <$> restOfLine)

parseBlock :: Parser T.Text
parseBlock = lexeme $ braces (T.pack <$> parseBlockBody 0)

parseBlockBody :: Int -> Parser String
parseBlockBody n = do
  c <- lookAhead anyChar
  case (c,n) of
    ('}', 0) -> return mempty
    ('}', _) -> (:) <$> anyChar <*> parseBlockBody (n-1)
    ('{', _) -> (:) <$> anyChar <*> parseBlockBody (n+1)
    _        -> (:) <$> anyChar <*> parseBlockBody n

restOfLine :: Parser T.Text
restOfLine = T.pack <$> (anyChar `manyTill` (void newline <|> eof))

parseExpectedStructure :: Parser StructureTest
parseExpectedStructure =
  lexstr "structure" *>
  (StructureTest <$> optimisePipeline <*> parseMetrics)

optimisePipeline :: Parser StructurePipeline
optimisePipeline = lexstr "distributed" *> pure distributePipelineConfig <|>
                   pure defaultPipelineConfig
  where defaultPipelineConfig =
          SOACSPipeline standardPipeline
        distributePipelineConfig =
          KernelsPipeline $
          standardPipeline >>>
          onePass extractKernels >>>
          onePass simplifyKernels

parseMetrics :: Parser AstMetrics
parseMetrics = braces $ fmap HM.fromList $ many $
               (,) <$> (T.pack <$> lexeme (many1 (satisfy constituent))) <*> parseNatural
  where constituent c = isAlpha c || c == '/'

testSpec :: Parser ProgramTest
testSpec =
  ProgramTest <$> parseDescription <*> parseTags <*> parseAction <*> optional parseExpectedStructure

readTestSpec :: SourceName -> T.Text -> Either ParseError ProgramTest
readTestSpec = parse $ testSpec <* eof

commentPrefix :: T.Text
commentPrefix = T.pack "--"

fixPosition :: ParseError -> ParseError
fixPosition err =
  let newpos = incSourceColumn (errorPos err) $ T.length commentPrefix
  in setErrorPos newpos err

-- | Read the test specification from the given Futhark program.
-- Note: will call 'error' on parse errors.
testSpecFromFile :: FilePath -> IO ProgramTest
testSpecFromFile path = do
  s <- T.unlines .
       map (T.drop 2) .
       takeWhile (commentPrefix `T.isPrefixOf`) .
       T.lines <$>
       T.readFile path
  case readTestSpec path s of
    Left err -> error $ show $ fixPosition err
    Right v  -> return v

-- | Try to parse a several core Futhark values from a string.  The
-- 'SourceName' parameter is used for error messages.
valuesFromString :: SourceName -> String -> Either F.ParseError [Value]
valuesFromString srcname s =
  fmap concat $ mapM internalise =<< F.parseValues srcname (T.pack s)
  where internalise v =
          maybe (Left $ F.ParseError $ "Invalid input value: " ++ pretty v) Right $
          internaliseValue v

-- | Try to parse a several core Futhark values from a text.  The
-- 'SourceName' parameter is used for error messages.
valuesFromText :: SourceName -> T.Text -> Either F.ParseError [Value]
valuesFromText srcname = valuesFromString srcname . T.unpack

-- | Get the actual core Futhark values corresponding to a 'Values'
-- specification.  The 'FilePath' is the directory which file paths
-- are read relative to.
getValues :: MonadIO m => FilePath -> Values -> m [Value]
getValues _ (Values vs) =
  return vs
getValues dir (InFile file) = do
  s <- liftIO $ T.readFile file'
  case valuesFromText file' s of
    Left e   -> fail $ show e
    Right vs -> return vs
  where file' = dir </> file

getValuesText :: MonadIO m => FilePath -> Values -> m T.Text
getValuesText _ (Values vs) =
  return $ T.unlines $ map prettyText vs
getValuesText dir (InFile file) =
  liftIO $ T.readFile file'
  where file' = dir </> file

data Mismatch = PrimValueMismatch Int PrimValue PrimValue
              | ArrayLengthMismatch Int Int Int
              | TypeMismatch Int Type Type
              | ValueCountMismatch Int Int

instance Show Mismatch where
  show (PrimValueMismatch i got expected) =
    explainMismatch i "" got expected
  show (ArrayLengthMismatch i got expected) =
    explainMismatch i "array of length" got expected
  show (TypeMismatch i got expected) =
    explainMismatch i "value of type" got expected
  show (ValueCountMismatch got expected) =
    "Expected " ++ show expected ++ " values, got " ++ show got

explainMismatch :: Pretty a => Int -> String -> a -> a -> String
explainMismatch i what got expected =
  "Value " ++ show i ++ " expected " ++ what ++ pretty expected ++ ", got " ++ pretty got

compareValues :: [Value] -> [Value] -> Maybe Mismatch
compareValues got expected
  | n /= m = Just $ ValueCountMismatch n m
  | otherwise = case catMaybes $ zipWith3 compareValue [0..] got expected of
    e : _ -> Just e
    []    -> Nothing
  where n = length got
        m = length expected

compareValue :: Int -> Value -> Value -> Maybe Mismatch
compareValue i (PrimVal got) (PrimVal expected)
  | comparePrimValue minTolerance got expected = Nothing
  | otherwise = Just $ PrimValueMismatch i got expected
compareValue i (ArrayVal got _ _) (ArrayVal expected _ _)
  | A.bounds got == A.bounds expected =
      uncurry (PrimValueMismatch i) <$>
        find (not . uncurry (comparePrimValue tol)) (zip (A.elems got) (A.elems expected))
  | otherwise =
      Just $ ArrayLengthMismatch i (snd $ A.bounds got) (snd $ A.bounds expected)
  where tol = tolerance expected
compareValue i got expected =
  Just $ TypeMismatch i (valueType got) (valueType expected)

comparePrimValue :: Double -> PrimValue -> PrimValue -> Bool
comparePrimValue tol (FloatValue (Float32Value x)) (FloatValue (Float32Value y)) =
  compareFractional tol x y
comparePrimValue tol  (FloatValue (Float64Value x)) (FloatValue (Float64Value y)) =
  compareFractional tol x y
comparePrimValue tol  (FloatValue (Float64Value x)) (FloatValue (Float32Value y)) =
  compareFractional tol x (floatToDouble y)
comparePrimValue tol  (FloatValue (Float32Value x)) (FloatValue (Float64Value y)) =
  compareFractional tol (floatToDouble x) y
comparePrimValue _ x y =
  x == y

compareFractional :: (Show num, Ord num, Fractional num, Show tol, Real tol) =>
                     tol -> num -> num -> Bool
compareFractional tol x y =
  diff < tol'
  where diff = abs $ x - y
        tol' = fromRational $ toRational tol

minTolerance :: Fractional a => a
minTolerance = 0.002 -- 0.2%

tolerance :: A.Array Int PrimValue -> Double
tolerance = foldl' tolerance' minTolerance
  where tolerance' t (FloatValue (Float32Value v)) = max t $ minTolerance * floatToDouble v
        tolerance' t (FloatValue (Float64Value v)) = max t $ minTolerance * v
        tolerance' t _                             = t

floatToDouble :: Float -> Double
floatToDouble x =
  let (m,n) = decodeFloat x
  in encodeFloat m n
