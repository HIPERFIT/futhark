{
-- | Futhark parser written with Happy.
module Language.Futhark.Parser.Parser
  ( prog
  , expression
  , pattern
  , lambda
  , futharktype
  , intValue
  , boolValue
  , charValue
  , stringValue
  , certValue
  , arrayValue
  , tupleValue
  , anyValue
  , anyValues
  , ParserEnv (..)
  , ParserMonad
  , ReadLineMonad(..)
  , getLinesFromIO
  , getLinesFromStrings
  , getNoLines
  )
  where

import Control.Applicative
import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Trans.State
import Control.Applicative ((<$>), (<*>))
import Data.Array
import Data.Maybe (fromMaybe)
import Data.Loc hiding (L) -- Lexer has replacements.
import qualified Data.HashMap.Lazy as HM

import Language.Futhark.Syntax hiding (ID)
import Language.Futhark.Attributes
import Language.Futhark.Parser.Lexer

}

%name prog Prog
%name expression Exp
%name pattern TupId
%name lambda FunAbstr
%name futharktype Type
%name intValue IntValue
%name boolValue LogValue
%name charValue CharValue
%name certValue CertValue
%name stringValue StringValue
%name arrayValue ArrayValue
%name tupleValue TupleValue
%name anyValue Value
%name anyValues CatValues

%tokentype { L Token }
%error { parseError }
%monad { ParserMonad }
%lexer { lexer } { L _ EOF }

%token
      if              { L $$ IF }
      then            { L $$ THEN }
      else            { L $$ ELSE }
      let             { L $$ LET }
      loop            { L $$ LOOP }
      in              { L $$ IN }
      int             { L $$ INT }
      bool            { L $$ BOOL }
      cert            { L $$ CERT }
      char            { L $$ CHAR }
      real            { L $$ REAL }

      id              { L _ (ID _) }

      intlit          { L _ (INTLIT _) }
      reallit         { L _ (REALLIT _) }
      stringlit       { L _ (STRINGLIT _) }
      charlit         { L _ (CHARLIT _) }

      '+'             { L $$ PLUS }
      '-'             { L $$ MINUS }
      '*'             { L $$ TIMES }
      '/'             { L $$ DIVIDE }
      '%'             { L $$ MOD }
      '//'            { L $$ QUOT }
      '%%'            { L $$ REM }
      '='             { L $$ EQU }
      '=='            { L $$ EQU2 }
      '<'             { L $$ LTH }
      '>'             { L $$ GTH }
      '<='            { L $$ LEQ }
      '>='            { L $$ GEQ }
      pow             { L $$ POW }
      '<<'            { L $$ SHIFTL }
      '>>'            { L $$ SHIFTR }
      '|'             { L $$ BOR }
      '&'             { L $$ BAND }
      '^'             { L $$ XOR }
      '('             { L $$ LPAR }
      ')'             { L $$ RPAR }
      '['             { L $$ LBRACKET }
      ']'             { L $$ RBRACKET }
      '{'             { L $$ LCURLY }
      '}'             { L $$ RCURLY }
      ','             { L $$ COMMA }
      '_'             { L $$ UNDERSCORE }
      '!'             { L $$ BANG }
      fun             { L $$ FUN }
      fn              { L $$ FN }
      '=>'            { L $$ ARROW }
      '<-'            { L $$ SETTO }
      for             { L $$ FOR }
      do              { L $$ DO }
      with            { L $$ WITH }
      iota            { L $$ IOTA }
      size            { L $$ SIZE }
      replicate       { L $$ REPLICATE }
      map             { L $$ MAP }
      concatMap       { L $$ CONCATMAP }
      reduce          { L $$ REDUCE }
      reshape         { L $$ RESHAPE }
      rearrange       { L $$ REARRANGE }
      stripe          { L $$ STRIPE }
      unstripe          { L $$ UNSTRIPE }
      transpose       { L $$ TRANSPOSE }
      zipWith         { L $$ ZIPWITH }
      zip             { L $$ ZIP }
      unzip           { L $$ UNZIP }
      scan            { L $$ SCAN }
      split           { L $$ SPLIT }
      concat          { L $$ CONCAT }
      filter          { L $$ FILTER }
      partition       { L $$ PARTITION }
      redomap         { L $$ REDOMAP }
      true            { L $$ TRUE }
      false           { L $$ FALSE }
      checked         { L $$ CHECKED }
      '~'             { L $$ TILDE }
      abs             { L $$ ABS }
      signum          { L $$ SIGNUM }
      '&&'            { L $$ AND }
      '||'            { L $$ OR }
      op              { L $$ OP }
      empty           { L $$ EMPTY }
      copy            { L $$ COPY }
      while           { L $$ WHILE }
      streamMap       { L $$ STREAM_MAP }
      streamMapMax    { L $$ STREAM_MAPMAX }
      streamMapPer    { L $$ STREAM_MAPPER }
      streamMapPerMax { L $$ STREAM_MAPPERMAX }
      streamRed       { L $$ STREAM_RED }
      streamRedMax    { L $$ STREAM_REDMAX }
      streamRedPer    { L $$ STREAM_REDPER }
      streamRedPerMax { L $$ STREAM_REDPERMAX }
      streamSeq       { L $$ STREAM_SEQ }
      streamSeqMax    { L $$ STREAM_SEQMAX }

%nonassoc ifprec letprec
%left '||'
%left '&&'
%left '&' '^' '|'
%left '<=' '>=' '>' '<' '=='

%left '<<' '>>'
%left '+' '-'

%left '*' '/' '%' '//' '%%'
%left pow
%nonassoc '~' '!' signum abs

%%

Prog :: { UncheckedProg }
     :   FunDecs { Prog $1 }
;

-- Note that this production does not include Minus.
BinOp :: { (BinOp, SrcLoc) }
      : '+'     { (Plus, $1) }
      | '*'     { (Times, $1) }
      | '/'     { (Divide, $1) }
      | '%'     { (Mod, $1) }
      | '//'    { (Quot, $1) }
      | '%%'    { (Rem, $1) }
      | '=='    { (Equal, $1) }
      | '<'     { (Less, $1) }
      | '<='    { (Leq, $1) }
      | '>'     { (Greater, $1) }
      | '>='    { (Geq, $1) }
      | '&&'    { (LogAnd, $1) }
      | '||'    { (LogOr, $1) }
      | pow     { (Pow, $1) }
      | '^'     { (Xor, $1) }
      | '&'     { (Band, $1) }
      | '|'     { (Bor, $1) }
      | '>>'    { (ShiftR, $1) }
      | '<<'    { (ShiftL, $1) }

UnOp :: { (UnOp, SrcLoc) }
     : '~' { (Complement, $1) }
     | '!' { (Not, $1) }
     | abs { (Abs, $1) }
     | signum { (Signum, $1) }

FunDecs : fun Fun FunDecs   { $2 : $3 }
        | fun Fun           { [$2] }
;

Fun :     Type id '(' TypeIds ')' '=' Exp
                        { let L pos (ID name) = $2 in (name, $1, $4, $7, pos) }
        | Type id '(' ')' '=' Exp
                        { let L pos (ID name) = $2 in (name, $1, [], $6, pos) }
;

Uniqueness : '*' { Unique }
           |     { Nonunique }

Type :: { UncheckedType }
        : BasicType     { Basic $1 }
        | ArrayType     { Array $1 }
        | '{' Types '}' { Tuple $2 }
;

DimDecl :: { DimDecl Name }
        : ',' id
          { let L _ (ID name) = $2
            in NamedDim name }
        | ',' intlit
          { let L _ (INTLIT n) = $2
            in ConstDim (fromIntegral n) }
        | { AnyDim }

ArrayType :: { UncheckedArrayType }
          : Uniqueness '[' BasicArrayRowType DimDecl ']'
            { let (ds, et) = $3
              in BasicArray et (ShapeDecl ($4:ds)) $1 NoInfo }
          | Uniqueness '[' TupleArrayRowType DimDecl ']'
            { let (ds, et) = $3
              in TupleArray et (ShapeDecl ($4:ds)) $1 }

BasicArrayRowType : BasicType
                    { ([], $1) }
                  | '[' BasicArrayRowType DimDecl ']'
                    { let (ds, et) = $2
                      in ($3:ds, et) }

TupleArrayRowType : '{' TupleArrayElemTypes '}'
                     { ([], $2) }
                  | '[' TupleArrayRowType DimDecl ']'
                     { let (ds, et) = $2
                       in ($3:ds, et) }

TupleArrayElemTypes : { [] }
                    | TupleArrayElemType
                      { [$1] }
                    | TupleArrayElemType ',' TupleArrayElemTypes
                      { $1 : $3 }

TupleArrayElemType : BasicType                   { BasicArrayElem $1 NoInfo }
                   | ArrayType                   { ArrayArrayElem $1 }
                   | '{' TupleArrayElemTypes '}' { TupleArrayElem $2 }

BasicType : int           { Int }
          | real          {% getRealType }
          | bool          { Bool }
          | cert          { Cert }
          | char          { Char }

Types : Type ',' Types { $1 : $3 }
      | Type           { [$1] }
      |                { [] }
;

TypeIds : Type id ',' TypeIds
                        { let L pos (ID name) = $2 in Ident name $1 pos : $4 }
        | Type id       { let L pos (ID name) = $2 in [Ident name $1 pos] }
;

Exp  :: { UncheckedExp }
     : intlit         { let L pos (INTLIT num) = $1 in Literal (BasicVal $ IntVal num) pos }
     | reallit        {% let L pos (REALLIT num) = $1 in (liftM2 (Literal . BasicVal) (getRealValue num) (pure pos)) }
     | charlit        { let L pos (CHARLIT char) = $1 in Literal (BasicVal $ CharVal char) pos }
     | stringlit      { let L pos (STRINGLIT s) = $1
                        in Literal (ArrayVal (arrayFromList $ map (BasicVal . CharVal) s) $ Basic Char) pos }
     | true           { Literal (BasicVal $ LogVal True) $1 }
     | false          { Literal (BasicVal $ LogVal False) $1 }
     | checked        { Literal (BasicVal Checked) $1 }
     | Id             { Var $1 }
     | empty '(' Type ')' { Literal (emptyArray $3) $1 }
     | '[' Exps ']'   { ArrayLit $2 NoInfo $1 }
     | TupleExp       { let (exps, pos) = $1 in TupLit exps pos }

     | Exp '+' Exp    { BinOp Plus $1 $3 NoInfo $2 }
     | Exp '-' Exp    { BinOp Minus $1 $3 NoInfo $2 }
     | Exp '*' Exp    { BinOp Times $1 $3 NoInfo $2 }
     | Exp '/' Exp    { BinOp Divide $1 $3 NoInfo $2 }
     | Exp '%' Exp    { BinOp Mod $1 $3 NoInfo $2 }
     | Exp '//' Exp   { BinOp Quot $1 $3 NoInfo $2 }
     | Exp '%%' Exp   { BinOp Rem $1 $3 NoInfo $2 }
     | '-' Exp %prec '~' { UnOp Negate $2 $1 }
     | '!' Exp        { UnOp Not $2 $1 }
     | '~' Exp        { UnOp Complement $2 $1 }
     | abs Exp        { UnOp Abs $2 $1 }
     | signum Exp     { UnOp Signum $2 $1 }
     | Exp pow Exp    { BinOp Pow $1 $3 NoInfo $2 }
     | Exp '>>' Exp   { BinOp ShiftR $1 $3 NoInfo $2 }
     | Exp '<<' Exp   { BinOp ShiftL $1 $3 NoInfo $2 }
     | Exp '&&' Exp   { BinOp LogAnd $1 $3 NoInfo $2 }
     | Exp '||' Exp   { BinOp LogOr $1 $3 NoInfo $2 }
     | Exp '&' Exp    { BinOp Band $1 $3 NoInfo $2 }
     | Exp '|' Exp    { BinOp Bor $1 $3 NoInfo $2 }
     | Exp '^' Exp    { BinOp Xor $1 $3 NoInfo $2 }

     | Exp '==' Exp   { BinOp Equal $1 $3 NoInfo $2 }
     | Exp '<' Exp    { BinOp Less $1 $3 NoInfo $2 }
     | Exp '<=' Exp   { BinOp Leq  $1 $3 NoInfo $2 }
     | Exp '>' Exp    { BinOp Greater $1 $3 NoInfo $2 }
     | Exp '>=' Exp   { BinOp Geq  $1 $3 NoInfo $2 }

     | if Exp then Exp else Exp %prec ifprec
                      { If $2 $4 $6 NoInfo $1 }

     | id '(' Exps ')'
                      {% let L pos (ID name) = $1 in do{
                            name' <- getFunName name;
                            return (Apply name' [ (arg, Observe) | arg <- $3 ] NoInfo pos)}
                      }
     | id '(' ')'     {% let L pos (ID name) = $1
                        in do { name' <- getFunName name; return (Apply name' [] NoInfo pos) } }

     | iota '(' Exp ')' { Iota $3 $1 }

     | size '(' NaturalInt ',' Exp ')'
                      { Size $3 $5 $1 }

     | replicate '(' Exp ',' Exp ')' { Replicate $3 $5 $1 }

     | reshape '(' '(' Exps ')' ',' Exp ')'
                      { Reshape $4 $7 $1 }

     | rearrange '(' '(' NaturalInts ')' ',' Exp ')'
                      { Rearrange $4 $7 $1 }

     | stripe '(' Exp ',' Exp ')'
                      { Stripe $3 $5 $1 }
     | unstripe '(' Exp ',' Exp ')'
                      { Unstripe $3 $5 $1 }

     | transpose '(' Exp ')' { Transpose 0 1 $3 $1 }

     | transpose '(' NaturalInt ',' SignedInt ',' Exp ')'
                      { Transpose $3 $5 $7 $1 }

     | split '(' '(' Exps ')' ',' Exp ')'
                      { Split $4 $7 $1 }

     | concat '(' Exp ',' Exps ')'
                      { Concat $3 $5 $1 }

     | reduce '(' FunAbstr ',' Exp ',' Exp ')'
                      { Reduce $3 $5 $7 $1 }

     | map '(' FunAbstr ',' Exp ')'
                      { Map $3 $5 $1 }

     | scan '(' FunAbstr ',' Exp ',' Exp ')'
                      { Scan $3 $5 $7 $1 }

     | zip '(' Exps2 ')'
                      { Zip (map (\x -> (x, NoInfo)) $3) $1 }

     | unzip '(' Exp ')'
                      { Unzip $3 [] $1 }

     | filter '(' FunAbstr ',' Exp ')'
                      { Filter $3 $5 $1 }

     | partition '(' FunAbstrsThenExp ')'
                      { Partition (fst $3) (snd $3) $1 }

     | redomap '(' FunAbstr ',' FunAbstr ',' Exp ',' Exp ')'
                      { Redomap $3 $5 $7 $9 $1 }

     | zipWith '(' FunAbstr ',' Exps2 ')'
                      { Map $3 (Zip (map (\x -> (x, NoInfo)) $5) $1) $1 }

     | concatMap '(' FunAbstr ',' Exp ',' Exps ')'
                      { ConcatMap $3 $5 $7 $1 }

     | concatMap '(' FunAbstr ',' Exp ')'
                      { ConcatMap $3 $5 [] $1 }

     | copy '(' Exp ')' { Copy $3 $1 }

     | '(' Exp ')' { $2 }

     | let Id '=' Exp in Exp %prec letprec
                      { LetPat (Id $2) $4 $6 $1 }

     | let '_' '=' Exp in Exp %prec letprec
                      { LetPat (Wildcard NoInfo $2) $4 $6 $1 }

     | let '{' TupIds '}' '=' Exp in Exp %prec letprec
                      { LetPat (TupId $3 $1) $6 $8 $1 }

     | let Id '=' Id with Index '<-' Exp in Exp %prec letprec
                      { LetWith $2 $4 $6 $8 $10 $1 }

     | let Id Index '=' Exp in Exp %prec letprec
                      { LetWith $2 $2 $3 $5 $7 $1 }

     | let Id '[' ']' '=' Exp in Exp %prec letprec
                      { LetWith $2 $2 [] $6 $8 $1 }

     | Id Index
                      { Index $1 $2 (srclocOf $1) }

     | loop '(' TupId ')' '=' for Id '<' Exp do Exp in Exp %prec letprec
                      {% liftM (\t -> DoLoop $3 t (ForLoop $7 $9) $11 $13 $1) (tupIdExp $3) }
     | loop '(' TupId '=' Exp ')' '=' for Id '<' Exp do Exp in Exp %prec letprec
                      { DoLoop $3 $5 (ForLoop $9 $11) $13 $15 $1 }

     | loop '(' TupId ')' '=' while Exp do Exp in Exp %prec letprec
                      {% liftM (\t -> DoLoop $3 t (WhileLoop $7) $9 $11 $1) (tupIdExp $3) }
     | loop '(' TupId '=' Exp ')' '=' while Exp do Exp in Exp %prec letprec
                      { DoLoop $3 $5 (WhileLoop $9) $11 $13 $1 }

     | streamMap       '(' FunAbstr ',' Exp ')'
                         { Stream (MapLike InOrder)  $3 $5 MinChunk $1 }
     | streamMapMax    '(' FunAbstr ',' Exp ')'
                         { Stream (MapLike InOrder)  $3 $5 MaxChunk $1 }
     | streamMapPer    '(' FunAbstr ',' Exp ')'
                         { Stream (MapLike Disorder) $3 $5 MinChunk $1 }
     | streamMapPerMax '(' FunAbstr ',' Exp ')'
                         { Stream (MapLike Disorder) $3 $5 MaxChunk $1 }

     | streamRed       '(' FunAbstr ',' FunAbstr ',' Exp ',' Exp ')'
                         { Stream (RedLike InOrder  $3 $7) $5 $9 MinChunk $1 }
     | streamRedMax    '(' FunAbstr ',' FunAbstr ',' Exp ',' Exp ')'
                         { Stream (RedLike InOrder  $3 $7) $5 $9 MaxChunk $1 }
     | streamRedPer    '(' FunAbstr ',' FunAbstr ',' Exp ',' Exp ')'
                         { Stream (RedLike Disorder $3 $7) $5 $9 MinChunk $1 }
     | streamRedPerMax '(' FunAbstr ',' FunAbstr ',' Exp ',' Exp ')'
                         { Stream (RedLike Disorder $3 $7) $5 $9 MaxChunk $1 }

     | streamSeq       '(' FunAbstr ',' Exp ',' Exp ')'
                         { Stream (Sequential $5) $3 $7 MinChunk $1 }
     | streamSeqMax    '(' FunAbstr ',' Exp ',' Exp ')'
                         { Stream (Sequential $5) $3 $7 MaxChunk $1 }

Index : '[' Exps ']'                  { $2 }

Exps : Exp ',' Exps { $1 : $3 }
     | Exp          { [$1] }

Exps2 : Exp ',' Exps2 { $1 : $3 }
      | Exp ',' Exp   { [$1, $3] }


TupleExp : '{' Exps '}' { ($2, $1) }
         | '{'      '}' { ([], $1) }

Id : id { let L loc (ID name) = $1 in Ident name NoInfo loc }

TupIds : TupId ',' TupIds  { $1 : $3 }
       | TupId             { [$1] }
       |                   { [] }
;

TupId : id { let L pos (ID name) = $1 in Id $ Ident name NoInfo pos }
      | '_' { Wildcard NoInfo $1 }
      | '{' TupIds '}' { TupId $2 $1 }

FunAbstr :: { UncheckedLambda }
         : fn Type '(' TypeIds ')' '=>' Exp
           { AnonymFun $4 $7 $2 $1 }
         | id '(' Exps ')'
           {% let L pos (ID name) = $1 in do {
             name' <- getFunName name; return (CurryFun name' $3 NoInfo pos) } }
         | id '(' ')'
           {% let L pos (ID name) = $1 in do {
             name' <- getFunName name; return (CurryFun name' [] NoInfo pos) } }
         | id
           {% let L pos (ID name) = $1 in do {
             name' <- getFunName name; return (CurryFun name' [] NoInfo pos ) } }
           -- Minus is handed explicitly here because I could figure
           -- out how to resolve the ambiguity with negation.
         | '-' Exp
           { CurryBinOpRight Minus $2 NoInfo $1 }
         | '-'
           { BinOpFun Minus NoInfo $1 }
         | Exp '-'
           { CurryBinOpLeft Minus $1 NoInfo (srclocOf $1) }
         | BinOp Exp
           { CurryBinOpRight (fst $1) $2 NoInfo (snd $1) }
         | Exp BinOp
           { CurryBinOpLeft (fst $2) $1 NoInfo (snd $2) }
         | BinOp
           { BinOpFun (fst $1) NoInfo (snd $1) }
         | UnOp
           { UnOpFun (fst $1) NoInfo (snd $1) }

FunAbstrsThenExp : FunAbstr ',' Exp              { ([$1], $3) }
                 | FunAbstr ',' FunAbstrsThenExp { ($1 : fst $3, snd $3) }

Value : IntValue { $1 }
      | RealValue { $1 }
      | CharValue { $1 }
      | StringValue { $1 }
      | LogValue { $1 }
      | ArrayValue { $1 }
      | TupleValue { $1 }

CatValues : Value CatValues { $1 : $2 }
          |                 { [] }

SignedInt :: { Int }
          :     intlit { let L _ (INTLIT num) = $1 in fromIntegral num  }
          | '-' intlit { let L _ (INTLIT num) = $2 in fromIntegral (-num) }

NaturalInt :: { Int }
           :  intlit { let L _ (INTLIT num) = $1 in fromIntegral num  }

NaturalInts :: { [Int] }
           : intlit                 { let L _ (INTLIT num) = $1 in [fromIntegral num] }
           | intlit ',' NaturalInts { let L _ (INTLIT num) = $1 in fromIntegral num : $3  }

IntValue : intlit        { let L pos (INTLIT num) = $1 in BasicVal $ IntVal num }
         | '-' intlit    { let L pos (INTLIT num) = $2 in BasicVal $ IntVal (-num) }
RealValue : reallit      {% let L pos (REALLIT num) = $1 in liftM BasicVal (getRealValue num) }
          | '-' reallit  {% let L pos (REALLIT num) = $2 in liftM BasicVal (getRealValue (-num)) }
CharValue : charlit      { let L pos (CHARLIT char) = $1 in BasicVal $ CharVal char }
StringValue : stringlit  { let L pos (STRINGLIT s) = $1 in ArrayVal (arrayFromList $ map (BasicVal . CharVal) s) $ Basic Char }
LogValue : true          { BasicVal $ LogVal True }
         | false          { BasicVal $ LogVal False }
CertValue : checked      { BasicVal Checked }
ArrayValue :  '[' Value ']'
             {% return $ ArrayVal (arrayFromList [$2]) $ removeNames $ toDecl $ valueType $2
             }
           |  '[' Value ',' Values ']'
             {% case combArrayTypes (valueType $2) $ map valueType $4 of
                  Nothing -> throwError "Invalid array value"
                  Just ts -> return $ ArrayVal (arrayFromList $ $2:$4) $ removeNames ts
             }
           | empty '(' Type ')'
             { emptyArray $3 }
TupleValue : '{' Values '}' { TupVal $2 }

Values : Value ',' Values { $1 : $3 }
       | Value            { [$1] }
       |                  { [] }

{

data ParserEnv = ParserEnv {
                 parserFile :: FilePath
               , parserRealType :: BasicType
               , parserRealFun :: Double -> BasicValue
               , parserFunMap :: HM.HashMap Name Name
               }

type ParserMonad a =
  ExceptT String (
    ReaderT ParserEnv (
       StateT [L Token] ReadLineMonad)) a

data ReadLineMonad a = Value a
                     | GetLine (String -> ReadLineMonad a)

readLineFromMonad :: ReadLineMonad String
readLineFromMonad = GetLine Value

instance Monad ReadLineMonad where
  return = Value
  Value x >>= f = f x
  GetLine g >>= f = GetLine $ \s -> g s >>= f

instance Functor ReadLineMonad where
  f `fmap` m = do x <- m
                  return $ f x

instance Applicative ReadLineMonad where
  (<*>) = ap

getLinesFromIO :: ReadLineMonad a -> IO a
getLinesFromIO (Value x) = return x
getLinesFromIO (GetLine f) = do
  s <- getLine
  getLinesFromIO $ f s

getLinesFromStrings :: [String] -> ReadLineMonad a -> Either String a
getLinesFromStrings _ (Value x) = Right x
getLinesFromStrings (x : xs) (GetLine f) = getLinesFromStrings xs $ f x
getLinesFromStrings [] (GetLine _) = Left "Ran out of input"

getNoLines :: ReadLineMonad a -> Either String a
getNoLines (Value x) = Right x
getNoLines (GetLine _) = Left "No extra lines"

combArrayTypes :: TypeBase Rank NoInfo Name
               -> [TypeBase Rank NoInfo Name]
               -> Maybe (TypeBase Rank NoInfo Name)
combArrayTypes t ts = foldM comb t ts
  where comb x y
          | x == y    = Just x
          | otherwise = Nothing

arrayFromList :: [a] -> Array Int a
arrayFromList l = listArray (0, length l-1) l

tupIdExp :: UncheckedTupIdent -> ParserMonad UncheckedExp
tupIdExp (Id ident) = return $ Var ident
tupIdExp (TupId pats loc) = TupLit <$> (mapM tupIdExp pats) <*> return loc
tupIdExp (Wildcard _ loc) = throwError $ "Cannot have wildcard at " ++ locStr loc

eof :: L Token
eof = L (SrcLoc $ Loc (Pos "" 0 0 0) (Pos "" 0 0 0)) EOF

getTokens :: ParserMonad [L Token]
getTokens = lift $ lift get

putTokens :: [L Token] -> ParserMonad ()
putTokens ts = lift $ lift $ put ts

getFilename :: ParserMonad FilePath
getFilename = lift $ asks parserFile

getRealType :: ParserMonad BasicType
getRealType = lift $ asks parserRealType

getRealValue :: Double -> ParserMonad BasicValue
getRealValue x = do f <- lift $ asks parserRealFun
                    return $ f x

getFunName :: Name -> ParserMonad Name
getFunName name = do substs <- lift $ asks parserFunMap
                     return $ HM.lookupDefault name name substs

readLine :: ParserMonad String
readLine = lift $ lift $ lift readLineFromMonad

lexer :: (L Token -> ParserMonad a) -> ParserMonad a
lexer cont = do
  ts <- getTokens
  case ts of
    [] -> do
      ended <- lift $ runExceptT $ cont eof
      case ended of
        Right x -> return x
        Left _ -> do
          ts' <- alexScanTokens <$> getFilename <*> readLine
          ts'' <- case ts' of Right x -> return x
                              Left e  -> throwError e
          case ts'' of
            [] -> cont eof
            xs -> do
              putTokens xs
              lexer cont
    (x : xs) -> do
      putTokens xs
      cont x

parseError :: L Token -> ParserMonad a
parseError (L _ EOF) = throwError "Parse error: End of file"
parseError tok       = throwError $ "Parse error at " ++ locStr (srclocOf tok)
}
