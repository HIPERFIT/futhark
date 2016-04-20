{
{-# LANGUAGE OverloadedStrings #-}
{-# OPTIONS_GHC -w #-}
-- | The Futhark lexer.  Takes a string, produces a list of tokens with position information.
module Language.Futhark.Parser.Lexer
  ( Token(..)
  , L(..)
  , scanTokens
  ) where

import qualified Data.ByteString.Lazy as BS
import qualified Data.Text as T
import qualified Data.Text.Encoding as T
import Data.Char (ord)
import Data.Loc hiding (L)
import Data.Int (Int8, Int16, Int32, Int64)
import Data.Word (Word8)
import Data.Bits
import Data.Function (fix)

import Language.Futhark.Core (Int8, Int16, Int32, Int64, Name, nameFromText)

}

%wrapper "monad-bytestring"

@charlit = ($printable#['\\]|\\($printable|[0-9]+))
@stringcharlit = ($printable#[\"\\]|\\($printable|[0-9]+)|\n)
@hexlit = 0[xX][0-9a-fA-F]+
@declit = [0-9]+
@intlit = @hexlit|@declit
@reallit = (([0-9]+("."[0-9]+)?))([eE][\+\-]?[0-9]+)?

tokens :-

  $white+                               ;
  "--"[^\n]*                            ;
  "&&"                     { tokenC AND }
  "||"                     { tokenC OR }
  ">>"                     { tokenC SHIFTR }
  ">>>"                    { tokenC ZSHIFTR }
  "<<"                     { tokenC SHIFTL }
  "=>"                     { tokenC ARROW }
  "<-"                     { tokenC SETTO }
  "<="                     { tokenC LEQ }
  ">="                     { tokenC GEQ }
  "+"                      { tokenC PLUS }
  "-"                      { tokenC MINUS }
  "~"                      { tokenC TILDE }
  "*"                      { tokenC TIMES }
  "**"                     { tokenC POW }
  "/"                      { tokenC DIVIDE }
  "%"                      { tokenC MOD }
  "//"                     { tokenC QUOT }
  "%%"                     { tokenC REM }
  "="                      { tokenC EQU }
  "=="                     { tokenC EQU2 }
  "!="                     { tokenC NEQU }
  "<"                      { tokenC LTH }
  ">"                      { tokenC GTH }
  "&"                      { tokenC BAND }
  "|"                      { tokenC BOR }
  "^"                      { tokenC XOR }
  "("                      { tokenC LPAR }
  ")"                      { tokenC RPAR }
  "["                      { tokenC LBRACKET }
  "]"                      { tokenC RBRACKET }
  "{"                      { tokenC LCURLY }
  "}"                      { tokenC RCURLY }
  ","                      { tokenC COMMA }
  "_"                      { tokenC UNDERSCORE }
  "!"                      { tokenC BANG }
  "."                      { tokenC DOT }
  @intlit i8               { tokenM $ fmap I8LIT . tryRead "i8" . T.takeWhile (/='i') }
  @intlit i16              { tokenM $ fmap I16LIT . tryRead "i16" . T.takeWhile (/='i') }
  @intlit i32              { tokenM $ fmap I32LIT . tryRead "i32" . T.takeWhile (/='i') }
  @intlit i64              { tokenM $ fmap I64LIT . tryRead "i64" . T.takeWhile (/='i') }
  @intlit u8               { tokenM $ fmap U8LIT . tryRead "u8" . T.takeWhile (/='u') }
  @intlit u16              { tokenM $ fmap U16LIT . tryRead "u16" . T.takeWhile (/='u') }
  @intlit u32              { tokenM $ fmap U32LIT . tryRead "u32" . T.takeWhile (/='u') }
  @intlit u64              { tokenM $ fmap U64LIT . tryRead "u64" . T.takeWhile (/='u') }
  @intlit                  { tokenM $ fmap INTLIT . tryRead "int" }
  @reallit f32             { tokenM $ fmap F32LIT . tryRead "f32" . T.takeWhile (/='f') }
  @reallit f64             { tokenM $ fmap F64LIT . tryRead "f64" . T.takeWhile (/='f') }
  @reallit                 { tokenM $ fmap REALLIT . tryRead "f64" }
  "'" @charlit "'"         { tokenM $ fmap CHARLIT . tryRead "char" }
  \" @stringcharlit* \"    { tokenM $ fmap STRINGLIT . tryRead "string"  }
  [a-zA-Z] [a-zA-Z0-9_']*  { tokenS keyword }

{

keyword :: T.Text -> Token
keyword s =
  case s of
    "if"           -> IF
    "then"         -> THEN
    "else"         -> ELSE
    "let"          -> LET
    "loop"         -> LOOP
    "in"           -> IN
    "with"         -> WITH
    "default"      -> DEFAULT
    "int"          -> INT
    "float"        -> FLOAT
    "i8"           -> I8
    "i16"          -> I16
    "i32"          -> I32
    "i64"          -> I64
    "u8"           -> U8
    "u16"          -> U16
    "u32"          -> U32
    "u64"          -> U64
    "f32"          -> F32
    "f64"          -> F64
    "bool"         -> BOOL
    "fun"          -> FUN
    "fn"           -> FN
    "for"          -> FOR
    "do"           -> DO
    "True"         -> TRUE
    "False"        -> FALSE
    "abs"          -> ABS
    "signum"       -> SIGNUM

    "iota"         -> IOTA
    "size"         -> SIZE
    "replicate"    -> REPLICATE
    "reshape"      -> RESHAPE
    "rearrange"    -> REARRANGE
    "transpose"    -> TRANSPOSE
    "map"          -> MAP
    "reduce"       -> REDUCE
    "reduceComm"   -> REDUCECOMM
    "zip"          -> ZIP
    "zipWith"      -> ZIPWITH
    "unzip"        -> UNZIP
    "unsafe"       -> UNSAFE
    "scan"         -> SCAN
    "split"        -> SPLIT
    "concat"       -> CONCAT
    "filter"       -> FILTER
    "partition"    -> PARTITION
    "empty"        -> EMPTY
    "copy"         -> COPY
    "while"        -> WHILE
    "streamMap"    -> STREAM_MAP
    "streamMapPer" -> STREAM_MAPPER
    "streamRed"    -> STREAM_RED
    "streamRedPer" -> STREAM_REDPER
    "streamSeq"    -> STREAM_SEQ
    "write"        -> WRITE
    "include"      -> INCLUDE
    "type"         -> TYPE
    "entry"        -> ENTRY
    _              -> ID $ nameFromText s

tryRead :: Read a => String -> T.Text -> Alex a
tryRead desc s = case reads s' of
  [(x, "")] -> return x
  _         -> fail $ "Invalid " ++ desc ++ " literal: " ++ T.unpack s
  where s' = T.unpack s

tokenC v  = tokenS $ const v

tokenS f = tokenM $ return . f

tokenM f (AlexPn addr line col, _, s, _) len = do
  x <- f $ T.decodeUtf8 $ BS.toStrict $ BS.take len s
  return (pos, pos, x)
  where pos = (line, col, addr)

alexEOF = return ((0,0,0), (0,0,0), EOF)

-- | A value tagged with a source location.
data L a = L SrcLoc a

instance Eq a => Eq (L a) where
  L _ x == L _ y = x == y

instance Located (L a) where
  locOf (L (SrcLoc loc) _) = loc

-- | A lexical token.  It does not itself contain position
-- information, so in practice the parser will consume tokens tagged
-- with a source position.
data Token = IF
           | THEN
           | ELSE
           | LET
           | LOOP
           | IN
           | INT
           | I8
           | I16
           | I32
           | I64
           | U8
           | U16
           | U32
           | U64
           | BOOL
           | CHAR
           | FLOAT
           | F32
           | F64
           | ID Name
           | STRINGLIT String
           | DEFAULT
           | INTLIT Int64
           | I8LIT Int8
           | I16LIT Int16
           | I32LIT Int32
           | I64LIT Int64
           | U8LIT Int8
           | U16LIT Int16
           | U32LIT Int32
           | U64LIT Int64
           | REALLIT Double
           | F32LIT Float
           | F64LIT Double
           | CHARLIT Char
           | PLUS
           | MINUS
           | TIMES
           | DIVIDE
           | MOD
           | QUOT
           | REM
           | EQU
           | EQU2
           | NEQU
           | LTH
           | GTH
           | LEQ
           | GEQ
           | POW
           | SHIFTL
           | SHIFTR
           | ZSHIFTR
           | BOR
           | BAND
           | XOR
           | LPAR
           | RPAR
           | LBRACKET
           | RBRACKET
           | LCURLY
           | RCURLY
           | COMMA
           | UNDERSCORE
           | FUN
           | FN
           | ARROW
           | SETTO
           | FOR
           | DO
           | WITH
           | SIZE
           | IOTA
           | REPLICATE
           | MAP
           | REDUCE
           | REDUCECOMM
           | RESHAPE
           | REARRANGE
           | TRANSPOSE
           | ZIPWITH
           | ZIP
           | UNZIP
           | UNSAFE
           | SCAN
           | SPLIT
           | CONCAT
           | FILTER
           | PARTITION
           | TRUE
           | FALSE
           | TILDE
           | AND
           | OR
           | EMPTY
           | COPY
           | WHILE
           | STREAM_MAP
           | STREAM_MAPPER
           | STREAM_RED
           | STREAM_REDPER
           | STREAM_SEQ
           | BANG
           | DOT
           | ABS
           | SIGNUM
           | WRITE
           | INCLUDE
           | ENTRY
           | TYPE
           | EOF
             deriving (Show, Eq)

-- The Alex wrapper only works on ByteStrings, so we have to encode
-- the Text as UTF-8.  Ugh.
scanTokens :: FilePath -> T.Text -> Either String [L Token]
scanTokens file str = runAlex (BS.fromStrict $ T.encodeUtf8 str) $ do
  fix $ \loop -> do
    tok <- alexMonadScan
    case tok of
      (start, end, EOF) ->
        return [L (pos start end) EOF]
      (start, end, t) -> do
        rest <- loop
        return $ L (pos start end) t : rest
  where pos start end = SrcLoc $ Loc (posnToPos start) (posnToPos end)
        posnToPos (line, col, addr) = Pos file line col addr
}
