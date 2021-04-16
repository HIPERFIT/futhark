{
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE Trustworthy #-}
-- | Futhark parser written with Happy.
module Language.Futhark.Parser.Parser
  ( prog
  , expression
  , modExpression
  , futharkType
  , anyValue
  , anyValues

  , ParserMonad
  , parse
  , ParseError(..)
  , parseDecOrExpIncrM
  )
  where

import Control.Monad
import Control.Monad.Trans
import Control.Monad.Except
import Control.Monad.Reader
import Control.Monad.Trans.State
import Data.Array
import qualified Data.Text as T
import Codec.Binary.UTF8.String (encode)
import Data.Char (ord)
import Data.Maybe (fromMaybe, fromJust)
import Data.List (genericLength)
import qualified Data.List.NonEmpty as NE
import qualified Data.Map.Strict as M
import Data.Monoid

import Language.Futhark.Syntax hiding (ID)
import Language.Futhark.Prop
import Language.Futhark.Pretty
import Language.Futhark.Parser.Lexer
import Futhark.Util.Pretty
import Futhark.Util.Loc hiding (L) -- Lexer has replacements.

}

%name prog Prog
%name futharkType TypeExp
%name expression Exp
%name modExpression ModExp
%name declaration Dec
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
      match           { L $$ MATCH }
      case            { L $$ CASE }

      id              { L _ (ID _) }
      'id['           { L _ (INDEXING _) }

      'qid['          { L _ (QUALINDEXING _ _) }

      'qid.('         { L _ (QUALPAREN _ _) }

      unop            { L _ (UNOP _) }
      qunop           { L _ (QUALUNOP _ _) }

      constructor     { L _ (CONSTRUCTOR _) }

      '.int'          { L _ (PROJ_INTFIELD _) }

      intlit          { L _ (INTLIT _) }
      i8lit           { L _ (I8LIT _) }
      i16lit          { L _ (I16LIT _) }
      i32lit          { L _ (I32LIT _) }
      i64lit          { L _ (I64LIT _) }
      u8lit           { L _ (U8LIT _) }
      u16lit          { L _ (U16LIT _) }
      u32lit          { L _ (U32LIT _) }
      u64lit          { L _ (U64LIT _) }
      floatlit        { L _ (FLOATLIT _) }
      f32lit          { L _ (F32LIT _) }
      f64lit          { L _ (F64LIT _) }
      stringlit       { L _ (STRINGLIT _) }
      charlit         { L _ (CHARLIT _) }

      '.'             { L $$ DOT }
      '..'            { L $$ TWO_DOTS }
      '...'           { L $$ THREE_DOTS }
      '..<'           { L $$ TWO_DOTS_LT }
      '..>'           { L $$ TWO_DOTS_GT }
      '='             { L $$ EQU }

      '*'             { L $$ ASTERISK }
      '-'             { L $$ NEGATE }
      '<'             { L $$ LTH }
      '^'             { L $$ HAT }
      '~'             { L $$ TILDE }
      '|'             { L $$ PIPE  }

      '+...'          { L _ (SYMBOL Plus _ _) }
      '-...'          { L _ (SYMBOL Minus _ _) }
      '*...'          { L _ (SYMBOL Times _ _) }
      '/...'          { L _ (SYMBOL Divide _ _) }
      '%...'          { L _ (SYMBOL Mod _ _) }
      '//...'         { L _ (SYMBOL Quot _ _) }
      '%%...'         { L _ (SYMBOL Rem _ _) }
      '==...'         { L _ (SYMBOL Equal _ _) }
      '!=...'         { L _ (SYMBOL NotEqual _ _) }
      '<...'          { L _ (SYMBOL Less _ _) }
      '>...'          { L _ (SYMBOL Greater _ _) }
      '<=...'         { L _ (SYMBOL Leq _ _) }
      '>=...'         { L _ (SYMBOL Geq _ _) }
      '**...'         { L _ (SYMBOL Pow _ _) }
      '<<...'         { L _ (SYMBOL ShiftL _ _) }
      '>>...'         { L _ (SYMBOL ShiftR _ _) }
      '|>...'         { L _ (SYMBOL PipeRight _ _) }
      '<|...'         { L _ (SYMBOL PipeLeft _ _) }
      '|...'          { L _ (SYMBOL Bor _ _) }
      '&...'          { L _ (SYMBOL Band _ _) }
      '^...'          { L _ (SYMBOL Xor _ _) }
      '||...'         { L _ (SYMBOL LogOr _ _) }
      '&&...'         { L _ (SYMBOL LogAnd _ _) }

      '('             { L $$ LPAR }
      ')'             { L $$ RPAR }
      ')['            { L $$ RPAR_THEN_LBRACKET }
      '{'             { L $$ LCURLY }
      '}'             { L $$ RCURLY }
      '['             { L $$ LBRACKET }
      ']'             { L $$ RBRACKET }
      '#['            { L $$ HASH_LBRACKET }
      ','             { L $$ COMMA }
      '_'             { L $$ UNDERSCORE }
      '\\'            { L $$ BACKSLASH }
      '\''            { L $$ APOSTROPHE }
      '\'^'           { L $$ APOSTROPHE_THEN_HAT }
      '\'~'           { L $$ APOSTROPHE_THEN_TILDE }
      '`'             { L $$ BACKTICK }
      entry           { L $$ ENTRY }
      '->'            { L $$ RIGHT_ARROW }
      ':'             { L $$ COLON }
      ':>'            { L $$ COLON_GT }
      '?'             { L $$ QUESTION_MARK  }
      for             { L $$ FOR }
      do              { L $$ DO }
      with            { L $$ WITH }
      assert          { L $$ ASSERT }
      true            { L $$ TRUE }
      false           { L $$ FALSE }
      while           { L $$ WHILE }
      include         { L $$ INCLUDE }
      import          { L $$ IMPORT }
      type            { L $$ TYPE }
      module          { L $$ MODULE }
      val             { L $$ VAL }
      open            { L $$ OPEN }
      local           { L $$ LOCAL }
      doc             { L _  (DOC _) }

%left bottom
%left ifprec letprec caseprec typeprec enumprec sumprec
%left ',' case id constructor '(' '{'
%right ':' ':>'
%right '...' '..<' '..>' '..'
%left '`'
%right '->'
%left with
%left '='
%left '|>...'
%right '<|...'
%left '||...'
%left '&&...'
%left '<=...' '>=...' '>...' '<' '<...' '==...' '!=...'
%left '&...' '^...' '^' '|...' '|'
%left '<<...' '>>...'
%left '+...' '-...' '-'
%left '*...' '*' '/...' '%...' '//...' '%%...'
%left '**...'
%left juxtprec
%left indexprec
%%

-- The main parser.

Doc :: { DocComment }
     : doc { let L loc (DOC s) = $1 in DocComment s loc }

-- Four cases to avoid ambiguities.
Prog :: { UncheckedProg }
      -- File begins with a file comment, followed by a Dec with a comment.
      : Doc Doc Dec_ Decs { Prog (Just $1) (addDoc $2 $3 : $4) }
      -- File begins with a file comment, followed by a Dec with no comment.
      | Doc Dec_ Decs     { Prog (Just $1) ($2 : $3) }
      -- File begins with a dec with no comment.
      | Dec_ Decs         { Prog Nothing ($1 : $2) }
      -- File is empty.
      |                   { Prog Nothing [] }
;

Dec :: { UncheckedDec }
    : Dec_              { $1 }
    | Doc Dec_          { addDoc $1 $2 }

Decs :: { [UncheckedDec] }
      :          { [] }
      | Dec Decs { $1 : $2 }

Dec_ :: { UncheckedDec }
    : Val               { ValDec $1 }
    | TypeAbbr          { TypeDec $1 }
    | SigBind           { SigDec $1 }
    | ModBind           { ModDec $1 }
    | open ModExp       { OpenDec $2 $1 }
    | import stringlit
      { let L _ (STRINGLIT s) = $2 in ImportDec s NoInfo (srcspan $1 $>) }
    | local Dec         { LocalDec $2 (srcspan $1 $>) }
    | '#[' AttrInfo ']' Dec_
                        { addAttr $2 $4 }

;

SigExp :: { UncheckedSigExp }
        : QualName            { let (v, loc) = $1 in SigVar v NoInfo loc }
        | '{' Specs '}'  { SigSpecs $2 (srcspan $1 $>) }
        | SigExp with TypeRef { SigWith $1 $3 (srcspan $1 $>) }
        | '(' SigExp ')'      { SigParens $2 (srcspan $1 $>) }
        | '(' id ':' SigExp ')' '->' SigExp
                              { let L _ (ID name) = $2
                                in SigArrow (Just name) $4 $7 (srcspan $1 $>) }
        | SigExp '->' SigExp  { SigArrow Nothing $1 $3 (srcspan $1 $>) }

TypeRef :: { TypeRefBase NoInfo Name }
         : QualName TypeParams '=' TypeExpTerm
           { TypeRef (fst $1) $2 (TypeDecl $4 NoInfo) (srcspan (snd $1) $>) }

SigBind :: { SigBindBase NoInfo Name }
         : module type id '=' SigExp
          { let L _ (ID name) = $3
            in SigBind name $5 Nothing (srcspan $1 $>) }

ModExp :: { UncheckedModExp }
        : ModExp ':' SigExp
          { ModAscript $1 $3 NoInfo (srcspan $1 $>) }
        | '\\' ModParam maybeAscription(SimpleSigExp) '->' ModExp
          { ModLambda $2 (fmap (,NoInfo) $3) $5 (srcspan $1 $>) }
        | import stringlit
          { let L _ (STRINGLIT s) = $2 in ModImport s NoInfo (srcspan $1 $>) }
        | ModExpApply
          { $1 }
        | ModExpAtom
          { $1 }


ModExpApply :: { UncheckedModExp }
             : ModExpAtom ModExpAtom %prec juxtprec
               { ModApply $1 $2 NoInfo NoInfo (srcspan $1 $>) }
             | ModExpApply ModExpAtom %prec juxtprec
               { ModApply $1 $2 NoInfo NoInfo (srcspan $1 $>) }

ModExpAtom :: { UncheckedModExp }
            : '(' ModExp ')'
              { ModParens $2 (srcspan $1 $>) }
            | QualName
              { let (v, loc) = $1 in ModVar v loc }
            | '{' Decs '}' { ModDecs $2 (srcspan $1 $>) }

SimpleSigExp :: { UncheckedSigExp }
             : QualName            { let (v, loc) = $1 in SigVar v NoInfo loc }
             | '(' SigExp ')'      { $2 }

ModBind :: { ModBindBase NoInfo Name }
         : module id ModParams maybeAscription(SigExp) '=' ModExp
           { let L floc (ID fname) = $2;
             in ModBind fname $3 (fmap (,NoInfo) $4) $6 Nothing (srcspan $1 $>)
           }

ModParam :: { ModParamBase NoInfo Name }
          : '(' id ':' SigExp ')' { let L _ (ID name) = $2 in ModParam name $4 NoInfo (srcspan $1 $>) }

ModParams :: { [ModParamBase NoInfo Name] }
           : ModParam ModParams { $1 : $2 }
           |                    { [] }

Liftedness :: { Liftedness }
            :     { Unlifted }
            | '~' { SizeLifted }
            | '^' { Lifted }

Spec :: { SpecBase NoInfo Name }
      : val id TypeParams ':' TypeExpDecl
        { let L loc (ID name) = $2
          in ValSpec name $3 $5 Nothing (srcspan $1 $>) }
      | val BindingBinOp TypeParams ':' TypeExpDecl
        { ValSpec $2 $3 $5 Nothing (srcspan $1 $>) }
      | val BindingUnOp TypeParams ':' TypeExpDecl
        { ValSpec $2 $3 $5 Nothing (srcspan $1 $>) }
      | TypeAbbr
        { TypeAbbrSpec $1 }

      | type Liftedness id TypeParams
        { let L _ (ID name) = $3
          in TypeSpec $2 name $4 Nothing (srcspan $1 $>) }
      | type Liftedness 'id[' id ']' TypeParams
        { let L _ (INDEXING name) = $3; L ploc (ID pname) = $4
          in TypeSpec $2 name (TypeParamDim pname ploc : $6) Nothing (srcspan $1 $>) }

      | module id ':' SigExp
        { let L _ (ID name) = $2
          in ModSpec name $4 Nothing (srcspan $1 $>) }
      | include SigExp
        { IncludeSpec $2 (srcspan $1 $>) }
      | Doc Spec
        { addDocSpec $1 $2 }
      | '#[' AttrInfo ']' Spec
        { addAttrSpec $2 $4 }

Specs :: { [SpecBase NoInfo Name] }
       : Spec Specs { $1 : $2 }
       |            { [] }

SizeBinder :: { SizeBinder Name }
            : '[' id ']' { let L _ (ID name) = $2 in SizeBinder name (srcspan $1 $>) }

SizeBinders1 :: { [SizeBinder Name] }
             : SizeBinder SizeBinders1 { $1 : $2 }
             | SizeBinder              { [$1] }

TypeParam :: { TypeParamBase Name }
           : '[' id ']' { let L _ (ID name) = $2 in TypeParamDim name (srcspan $1 $>) }
           | '\'' id { let L _ (ID name) = $2 in TypeParamType Unlifted name (srcspan $1 $>) }
           | '\'~' id { let L _ (ID name) = $2 in TypeParamType SizeLifted name (srcspan $1 $>) }
           | '\'^' id { let L _ (ID name) = $2 in TypeParamType Lifted name (srcspan $1 $>) }

TypeParams :: { [TypeParamBase Name] }
            : TypeParam TypeParams { $1 : $2 }
            |                      { [] }

UnOp :: { (QualName Name, SrcLoc) }
      : qunop { let L loc (QUALUNOP qs v) = $1 in (QualName qs v, loc) }
      | unop  { let L loc (UNOP v) = $1 in (qualName v, loc) }

-- Note that this production does not include Minus, but does include
-- operator sections.
BinOp :: { (QualName Name, SrcLoc) }
      : '+...'     { binOpName $1 }
      | '-...'     { binOpName $1 }
      | '*...'     { binOpName $1 }
      | '*'        { (qualName (nameFromString "*"), $1) }
      | '/...'     { binOpName $1 }
      | '%...'     { binOpName $1 }
      | '//...'    { binOpName $1 }
      | '%%...'    { binOpName $1 }
      | '==...'    { binOpName $1 }
      | '!=...'    { binOpName $1 }
      | '<...'     { binOpName $1 }
      | '<=...'    { binOpName $1 }
      | '>...'     { binOpName $1 }
      | '>=...'    { binOpName $1 }
      | '&&...'    { binOpName $1 }
      | '||...'    { binOpName $1 }
      | '**...'    { binOpName $1 }
      | '^...'     { binOpName $1 }
      | '^'        { (qualName (nameFromString "^"), $1) }
      | '&...'     { binOpName $1 }
      | '|...'     { binOpName $1 }
      | '|'        { (qualName (nameFromString "|"), $1) }
      | '>>...'    { binOpName $1 }
      | '<<...'    { binOpName $1 }
      | '<|...'    { binOpName $1 }
      | '|>...'    { binOpName $1 }
      | '<'        { (qualName (nameFromString "<"), $1) }
      | '`' QualName '`' { $2 }

BindingUnOp :: { Name }
      : UnOp {% let (QualName qs name, loc) = $1 in do
                   unless (null qs) $ parseErrorAt loc $
                     Just "Cannot use a qualified name in binding position."
                   return name }

BindingBinOp :: { Name }
      : BinOp {% let (QualName qs name, loc) = $1 in do
                   unless (null qs) $ parseErrorAt loc $
                     Just "Cannot use a qualified name in binding position."
                   return name }
      | '-'   { nameFromString "-" }

BindingId :: { (Name, SrcLoc) }
     : id                   { let L loc (ID name) = $1 in (name, loc) }
     | '(' BindingBinOp ')' { ($2, $1) }
     | '(' BindingUnOp ')'  { ($2, $1) }

Val    :: { ValBindBase NoInfo Name }
Val     : let BindingId TypeParams FunParams maybeAscription(TypeExpDecl) '=' Exp
          { let (name, _) = $2
            in ValBind (if name==defaultEntryPoint then Just NoInfo else Nothing) name (fmap declaredType $5) NoInfo
               $3 $4 $7 Nothing mempty (srcspan $1 $>)
          }

        | entry BindingId TypeParams FunParams maybeAscription(TypeExpDecl) '=' Exp
          { let (name, loc) = $2
            in ValBind (Just NoInfo) name (fmap declaredType $5) NoInfo
               $3 $4 $7 Nothing mempty (srcspan $1 $>) }

        | let FunParam BindingBinOp FunParam maybeAscription(TypeExpDecl) '=' Exp
          { ValBind Nothing $3 (fmap declaredType $5) NoInfo [] [$2,$4] $7
            Nothing mempty (srcspan $1 $>)
          }

        | let BindingUnOp TypeParams FunParams maybeAscription(TypeExpDecl) '=' Exp
          { ValBind Nothing $2 (fmap declaredType $5) NoInfo $3 $4 $7
            Nothing mempty (srcspan $1 $>)
          }

TypeExpDecl :: { TypeDeclBase NoInfo Name }
             : TypeExp %prec bottom { TypeDecl $1 NoInfo }

TypeAbbr :: { TypeBindBase NoInfo Name }
TypeAbbr : type Liftedness id TypeParams '=' TypeExpDecl
           { let L _ (ID name) = $3
              in TypeBind name $2 $4 $6 Nothing (srcspan $1 $>) }
         | type Liftedness 'id[' id ']' TypeParams '=' TypeExpDecl
           { let L loc (INDEXING name) = $3; L ploc (ID pname) = $4
             in TypeBind name $2 (TypeParamDim pname ploc:$6) $8 Nothing (srcspan $1 $>) }

TypeExp :: { UncheckedTypeExp }
         : '(' id ':' TypeExp ')' '->' TypeExp
           { let L _ (ID v) = $2 in TEArrow (Just v) $4 $7 (srcspan $1 $>) }
         | TypeExpTerm '->' TypeExp
           { TEArrow Nothing $1 $3 (srcspan $1 $>) }
         | '?' TypeExpDims '.' TypeExp { TEDim $2 $4 (srcspan $1 $>) }
         | TypeExpTerm %prec typeprec { $1 }

TypeExpDims :: { [Name] }
         : '[' id ']'             { let L _ (ID v) = $2 in [v] }
         | '[' id ']' TypeExpDims { let L _ (ID v) = $2 in v : $4 }

TypeExpTerm :: { UncheckedTypeExp }
         : '*' TypeExpTerm
           { TEUnique $2 (srcspan $1 $>) }
         | '[' DimExp ']' TypeExpTerm %prec indexprec
           { TEArray $4 $2 (srcspan $1 $>) }
         | '['  ']' TypeExpTerm %prec indexprec
           { TEArray $3 DimExpAny (srcspan $1 $>) }
         | TypeExpApply %prec sumprec { $1 }

         -- Errors
         | '[' DimExp ']' %prec bottom
           {% parseErrorAt (srcspan $1 $>) $ Just $
                unlines ["missing array row type.",
                         "Did you mean []"  ++ pretty $2 ++ "?"]
           }

SumType :: { UncheckedTypeExp }
SumType  : SumClauses %prec sumprec { let (cs, loc) = $1
                        in TESum cs loc }

SumClauses :: { ([(Name, [UncheckedTypeExp])], SrcLoc) }
            : SumClauses '|' SumClause %prec sumprec { let (cs, loc1) = $1;
                                             (c, ts, loc2) = $3
                                          in (cs++[(c, ts)], srcspan loc1 loc2) }
            | SumClause  %prec sumprec { let (n, ts, loc) = $1
                                        in ([(n, ts)], loc) }

SumClause :: { (Name, [UncheckedTypeExp], SrcLoc) }
           : SumClause TypeExpAtom { let (n, ts, loc) = $1
                                     in (n, ts ++ [$2], srcspan loc $>)}
           | Constr { (fst $1, [], snd $1) }

TypeExpApply :: { UncheckedTypeExp }
              : TypeExpApply TypeArg
                { TEApply $1 $2 (srcspan $1 $>) }
              | 'id[' DimExp ']'
                { let L loc (INDEXING v) = $1
                  in TEApply (TEVar (qualName v) loc) (TypeArgExpDim $2 loc) (srcspan $1 $>) }
              | 'qid[' DimExp ']'
                { let L loc (QUALINDEXING qs v) = $1
                  in TEApply (TEVar (QualName qs v) loc) (TypeArgExpDim $2 loc) (srcspan $1 $>) }
              | TypeExpAtom
                { $1 }

TypeExpAtom :: { UncheckedTypeExp }
             : '(' TypeExp ')'                { $2 }
             | '(' ')'                        { TETuple [] (srcspan $1 $>) }
             | '(' TypeExp ',' TupleTypes ')' { TETuple ($2:$4) (srcspan $1 $>) }
             | '{' '}'                        { TERecord [] (srcspan $1 $>) }
             | '{' FieldTypes1 '}'            { TERecord $2 (srcspan $1 $>) }
             | QualName                       { TEVar (fst $1) (snd $1) }
             | SumType                        { $1 }

Constr :: { (Name, SrcLoc) }
        : constructor { let L _ (CONSTRUCTOR c) = $1 in (c, srclocOf $1) }

TypeArg :: { TypeArgExp Name }
         : '[' DimExp ']' { TypeArgExpDim $2 (srcspan $1 $>) }
         | '[' ']'         { TypeArgExpDim DimExpAny (srcspan $1 $>) }
         | TypeExpAtom     { TypeArgExpType $1 }

FieldType :: { (Name, UncheckedTypeExp) }
FieldType : FieldId ':' TypeExp { (fst $1, $3) }

FieldTypes1 :: { [(Name, UncheckedTypeExp)] }
FieldTypes1 : FieldType                 { [$1] }
            | FieldType ',' FieldTypes1 { $1 : $3 }

TupleTypes :: { [UncheckedTypeExp] }
            : TypeExp                { [$1] }
            | TypeExp ',' TupleTypes { $1 : $3 }

DimExp :: { DimExp Name }
        : QualName
          { DimExpNamed (fst $1) (snd $1) }
        | intlit
          { let L loc (INTLIT n) = $1
            in DimExpConst (fromIntegral n) loc }

FunParam :: { PatternBase NoInfo Name }
FunParam : InnerPattern { $1 }

FunParams1 :: { (PatternBase NoInfo Name, [PatternBase NoInfo Name]) }
FunParams1 : FunParam            { ($1, []) }
           | FunParam FunParams1 { ($1, fst $2 : snd $2) }

FunParams :: { [PatternBase NoInfo Name] }
FunParams :                     { [] }
           | FunParam FunParams { $1 : $2 }

QualName :: { (QualName Name, SrcLoc) }
          : id FieldAccesses
            { let L vloc (ID v) = $1 in
              foldl (\(QualName qs v', loc) (y, yloc) ->
                      (QualName (qs ++ [v']) y, srcspan loc yloc))
                    (qualName v, vloc) $2 }

-- Expressions are divided into several layers.  The first distinction
-- (between Exp and Exp2) is to factor out ascription, which we do not
-- permit inside array indices operations (there is an ambiguity with
-- array slices).
Exp :: { UncheckedExp }
     : Exp ':' TypeExpDecl { Ascript $1 $3 (srcspan $1 $>) }
     | Exp ':>' TypeExpDecl { AppExp (Coerce $1 $3 (srcspan $1 $>)) NoInfo }
     | Exp2 %prec ':'      { $1 }

Exp2 :: { UncheckedExp }
     : if Exp then Exp else Exp %prec ifprec
                      { AppExp (If $2 $4 $6 (srcspan $1 $>)) NoInfo }

     | loop Pattern LoopForm do Exp %prec ifprec
         {% fmap (\t -> AppExp (DoLoop [] $2 t $3 $5 (srcspan $1 $>)) NoInfo) (patternExp $2) }

     | loop Pattern '=' Exp LoopForm do Exp %prec ifprec
         { AppExp (DoLoop [] $2 $4 $5 $7 (srcspan $1 $>)) NoInfo }

     | LetExp %prec letprec { $1 }

     | MatchExp { $1 }

     | assert Atom Atom    { Assert $2 $3 NoInfo (srcspan $1 $>) }
     | '#[' AttrInfo ']' Exp %prec bottom
                           { Attr $2 $4 (srcspan $1 $>) }

     | Exp2 '+...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '-...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '-' Exp2       { binOp $1 (L $2 (SYMBOL Minus [] (nameFromString "-"))) $3 }
     | Exp2 '*...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '*' Exp2       { binOp $1 (L $2 (SYMBOL Times [] (nameFromString "*"))) $3 }
     | Exp2 '/...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '%...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '//...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '%%...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '**...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '>>...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '<<...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '&...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '|...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '|' Exp2       { binOp $1 (L $2 (SYMBOL Bor [] (nameFromString "|"))) $3 }
     | Exp2 '&&...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '||...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '^...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '^' Exp2       { binOp $1 (L $2 (SYMBOL Xor [] (nameFromString "^"))) $3 }
     | Exp2 '==...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '!=...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '<...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '<=...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '>...' Exp2    { binOp $1 $2 $3 }
     | Exp2 '>=...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '|>...' Exp2   { binOp $1 $2 $3 }
     | Exp2 '<|...' Exp2   { binOp $1 $2 $3 }

     | Exp2 '<' Exp2              { binOp $1 (L $2 (SYMBOL Less [] (nameFromString "<"))) $3 }
     | Exp2 '`' QualName '`' Exp2 { AppExp (BinOp $3 NoInfo ($1, NoInfo) ($5, NoInfo) (srcspan $1 $>)) NoInfo }

     | Exp2 '...' Exp2           { AppExp (Range $1 Nothing (ToInclusive $3) (srcspan $1 $>)) NoInfo }
     | Exp2 '..<' Exp2           { AppExp (Range $1 Nothing (UpToExclusive $3) (srcspan $1 $>)) NoInfo }
     | Exp2 '..>' Exp2           { AppExp (Range $1 Nothing (DownToExclusive $3)  (srcspan $1 $>)) NoInfo }
     | Exp2 '..' Exp2 '...' Exp2 { AppExp (Range $1 (Just $3) (ToInclusive $5) (srcspan $1 $>)) NoInfo }
     | Exp2 '..' Exp2 '..<' Exp2 { AppExp (Range $1 (Just $3) (UpToExclusive $5) (srcspan $1 $>)) NoInfo }
     | Exp2 '..' Exp2 '..>' Exp2 { AppExp (Range $1 (Just $3) (DownToExclusive $5) (srcspan $1 $>)) NoInfo }
     | Exp2 '..' Atom            {% twoDotsRange $2 }
     | Atom '..' Exp2            {% twoDotsRange $2 }
     | '-' Exp2
       { Negate $2 $1 }

     | Exp2 with '[' DimIndices ']' '=' Exp2
       { Update $1 $4 $7 (srcspan $1 $>) }

     | Exp2 with FieldAccesses_ '=' Exp2
       { RecordUpdate $1 (map fst $3) $5 NoInfo (srcspan $1 $>) }

     | '\\' FunParams1 maybeAscription(TypeExpTerm) '->' Exp %prec letprec
       { Lambda (fst $2 : snd $2) $5 $3 NoInfo (srcspan $1 $>) }

     | Apply_ { $1 }

Apply_ :: { UncheckedExp }
       : ApplyList {% applyExp $1 }

ApplyList :: { [UncheckedExp] }
          : ApplyList Atom %prec juxtprec
            { $1 ++ [$2] }
          | UnOp Atom %prec juxtprec
            { [Var (fst $1) NoInfo (snd $1), $2] }
          | Atom %prec juxtprec
            { [$1] }

Atom :: { UncheckedExp }
Atom : PrimLit        { Literal (fst $1) (snd $1) }
     | Constr         { Constr (fst $1) [] NoInfo (snd $1) }
     | charlit        { let L loc (CHARLIT x) = $1
                        in IntLit (toInteger (ord x)) NoInfo loc }
     | intlit         { let L loc (INTLIT x) = $1 in IntLit x NoInfo loc }
     | floatlit       { let L loc (FLOATLIT x) = $1 in FloatLit x NoInfo loc }
     | stringlit      { let L loc (STRINGLIT s) = $1 in
                        StringLit (encode s) loc }
     | '(' Exp ')' FieldAccesses
       { foldl (\x (y, _) -> Project y x NoInfo (srclocOf x))
               (Parens $2 (srcspan $1 ($3:map snd $>)))
               $4 }
     | '(' Exp ')[' DimIndices ']'    { AppExp (Index (Parens $2 $1) $4 (srcspan $1 $>)) NoInfo }
     | '(' Exp ',' Exps1 ')'          { TupLit ($2 : fst $4 : snd $4) (srcspan $1 $>) }
     | '('      ')'                   { TupLit [] (srcspan $1 $>) }
     | '[' Exps1 ']'                  { ArrayLit (fst $2:snd $2) NoInfo (srcspan $1 $>) }
     | '['       ']'                  { ArrayLit [] NoInfo (srcspan $1 $>) }

     | QualVarSlice FieldAccesses
       { let ((v, vloc),slice,loc) = $1
         in foldl (\x (y, _) -> Project y x NoInfo (srcspan x (srclocOf x)))
                  (AppExp (Index (Var v NoInfo vloc) slice (srcspan vloc loc)) NoInfo)
                  $2 }
     | QualName
       { Var (fst $1) NoInfo (snd $1) }
     | '{' Fields '}' { RecordLit $2 (srcspan $1 $>) }
     | 'qid.(' Exp ')'
       { let L loc (QUALPAREN qs name) = $1 in
         QualParens (QualName qs name, loc) $2 (srcspan $1 $>) }

     -- Operator sections.
     | '(' UnOp ')'
        { Var (fst $2) NoInfo (srcspan (snd $2) $>) }
     | '(' '-' ')'
        { OpSection (qualName (nameFromString "-")) NoInfo (srcspan $1 $>) }
     | '(' Exp2 '-' ')'
       { OpSectionLeft (qualName (nameFromString "-"))
         NoInfo $2 (NoInfo, NoInfo) (NoInfo, NoInfo) (srcspan $1 $>) }
     | '(' BinOp Exp2 ')'
       { OpSectionRight (fst $2) NoInfo $3 (NoInfo, NoInfo) NoInfo (srcspan $1 $>) }
     | '(' Exp2 BinOp ')'
       { OpSectionLeft (fst $3) NoInfo $2 (NoInfo, NoInfo) (NoInfo, NoInfo) (srcspan $1 $>) }
     | '(' BinOp ')'
       { OpSection (fst $2) NoInfo (srcspan $1 $>) }

     | '(' FieldAccess FieldAccesses ')'
       { ProjectSection (map fst ($2:$3)) NoInfo (srcspan $1 $>) }

     | '(' '.' '[' DimIndices ']' ')'
       { IndexSection $4 NoInfo (srcspan $1 $>) }


PrimLit :: { (PrimValue, SrcLoc) }
        : true   { (BoolValue True, $1) }
        | false  { (BoolValue False, $1) }

        | i8lit   { let L loc (I8LIT num)  = $1 in (SignedValue $ Int8Value num, loc) }
        | i16lit  { let L loc (I16LIT num) = $1 in (SignedValue $ Int16Value num, loc) }
        | i32lit  { let L loc (I32LIT num) = $1 in (SignedValue $ Int32Value num, loc) }
        | i64lit  { let L loc (I64LIT num) = $1 in (SignedValue $ Int64Value num, loc) }

        | u8lit  { let L loc (U8LIT num)  = $1 in (UnsignedValue $ Int8Value $ fromIntegral num, loc) }
        | u16lit { let L loc (U16LIT num) = $1 in (UnsignedValue $ Int16Value $ fromIntegral num, loc) }
        | u32lit { let L loc (U32LIT num) = $1 in (UnsignedValue $ Int32Value $ fromIntegral num, loc) }
        | u64lit { let L loc (U64LIT num) = $1 in (UnsignedValue $ Int64Value $ fromIntegral num, loc) }

        | f32lit { let L loc (F32LIT num) = $1 in (FloatValue $ Float32Value num, loc) }
        | f64lit { let L loc (F64LIT num) = $1 in (FloatValue $ Float64Value num, loc) }

Exps1 :: { (UncheckedExp, [UncheckedExp]) }
       : Exps1_ { case reverse (snd $1 : fst $1) of
                    []   -> (snd $1, [])
                    y:ys -> (y, ys) }

Exps1_ :: { ([UncheckedExp], UncheckedExp) }
        : Exps1_ ',' Exp { (snd $1 : fst $1, $3) }
        | Exp            { ([], $1) }

FieldAccess :: { (Name, SrcLoc) }
             : '.' id { let L loc (ID f) = $2 in (f, loc) }
             | '.int' { let L loc (PROJ_INTFIELD x) = $1 in (x, loc) }

FieldAccesses :: { [(Name, SrcLoc)] }
               : FieldAccess FieldAccesses { $1 : $2 }
               |                           { [] }

FieldAccesses_ :: { [(Name, SrcLoc)] }
               : FieldId FieldAccesses { (fst $1, snd $1) : $2 }

Field :: { FieldBase NoInfo Name }
       : FieldId '=' Exp { RecordFieldExplicit (fst $1) $3 (srcspan (snd $1) $>) }
       | id              { let L loc (ID s) = $1 in RecordFieldImplicit s NoInfo loc }

Fields :: { [FieldBase NoInfo Name] }
        : Fields1 { $1 }
        |         { [] }

Fields1 :: { [FieldBase NoInfo Name] }
        : Field ',' Fields1 { $1 : $3 }
        | Field             { [$1] }

LetExp :: { UncheckedExp }
     : let SizeBinders1 Pattern '=' Exp LetBody
       { AppExp (LetPat $2 $3 $5 $6 (srcspan $1 $>)) NoInfo }
     | let Pattern '=' Exp LetBody
       { AppExp (LetPat [] $2 $4 $5 (srcspan $1 $>)) NoInfo }

     | let id TypeParams FunParams1 maybeAscription(TypeExpDecl) '=' Exp LetBody
       { let L _ (ID name) = $2
         in AppExp (LetFun name ($3, fst $4 : snd $4, (fmap declaredType $5), NoInfo, $7)
                    $8 (srcspan $1 $>))
                   NoInfo}

     | let VarSlice '=' Exp LetBody
       { let ((v,_),slice,loc) = $2; ident = Ident v NoInfo loc
         in AppExp (LetWith ident ident slice $4 $5 (srcspan $1 $>)) NoInfo }

LetBody :: { UncheckedExp }
    : in Exp %prec letprec { $2 }
    | LetExp %prec letprec { $1 }
    | error {% throwError "Unexpected end of file - missing \"in\"?" }

MatchExp :: { UncheckedExp }
          : match Exp Cases
            { let loc = srcspan $1 (NE.toList $>)
              in AppExp (Match $2 $> loc) NoInfo }

Cases :: { NE.NonEmpty (CaseBase NoInfo Name) }
       : Case  %prec caseprec { $1 NE.:| [] }
       | Case Cases           { NE.cons $1 $2 }

Case :: { CaseBase NoInfo Name }
      : case CPattern '->' Exp
        { let loc = srcspan $1 $> in CasePat $2 $> loc }

CPattern :: { PatternBase NoInfo Name }
          : CInnerPattern ':' TypeExpDecl { PatternAscription $1 $3 (srcspan $1 $>) }
          | CInnerPattern                 { $1 }
          | Constr ConstrFields           { let (n, loc) = $1;
                                                loc' = srcspan loc $>
                                            in PatternConstr n NoInfo $2 loc'}

CPatterns1 :: { [PatternBase NoInfo Name] }
           : CPattern               { [$1] }
           | CPattern ',' CPatterns1 { $1 : $3 }

CInnerPattern :: { PatternBase NoInfo Name }
               : id                                 { let L loc (ID name) = $1 in Id name NoInfo loc }
               | '(' BindingBinOp ')'               { Id $2 NoInfo (srcspan $1 $>) }
               | '(' BindingUnOp ')'                { Id $2 NoInfo (srcspan $1 $>) }
               | '_'                                { Wildcard NoInfo $1 }
               | '(' ')'                            { TuplePattern [] (srcspan $1 $>) }
               | '(' CPattern ')'                   { PatternParens $2 (srcspan $1 $>) }
               | '(' CPattern ',' CPatterns1 ')'    { TuplePattern ($2:$4) (srcspan $1 $>) }
               | '{' CFieldPatterns '}'             { RecordPattern $2 (srcspan $1 $>) }
               | CaseLiteral                        { PatternLit (fst $1) NoInfo (snd $1) }
               | Constr                             { let (n, loc) = $1
                                                      in PatternConstr n NoInfo [] loc }

ConstrFields :: { [PatternBase NoInfo Name] }
              : CInnerPattern                { [$1] }
              | ConstrFields CInnerPattern   { $1 ++ [$2] }

CFieldPattern :: { (Name, PatternBase NoInfo Name) }
               : FieldId '=' CPattern
               { (fst $1, $3) }
               | FieldId ':' TypeExpDecl
               { (fst $1, PatternAscription (Id (fst $1) NoInfo (snd $1)) $3 (srcspan (snd $1) $>)) }
               | FieldId
               { (fst $1, Id (fst $1) NoInfo (snd $1)) }

CFieldPatterns :: { [(Name, PatternBase NoInfo Name)] }
                : CFieldPatterns1 { $1 }
                |                { [] }

CFieldPatterns1 :: { [(Name, PatternBase NoInfo Name)] }
                 : CFieldPattern ',' CFieldPatterns1 { $1 : $3 }
                 | CFieldPattern                    { [$1] }

CaseLiteral :: { (PatLit, SrcLoc) }
             : PrimLit  { (PatLitPrim (fst $1), snd $1) }
             | charlit  { let L loc (CHARLIT x) = $1
                          in (PatLitInt (toInteger (ord x)), loc) }
             | intlit   { let L loc (INTLIT x) = $1 in (PatLitInt x, loc) }
             | floatlit { let L loc (FLOATLIT x) = $1 in (PatLitFloat x, loc) }

LoopForm :: { LoopFormBase NoInfo Name }
LoopForm : for VarId '<' Exp
           { For $2 $4 }
         | for Pattern in Exp
           { ForIn $2 $4 }
         | while Exp
           { While $2 }

VarSlice :: { ((Name, SrcLoc), UncheckedSlice, SrcLoc) }
          : 'id[' DimIndices ']'
            { let L vloc (INDEXING v) = $1
              in ((v, vloc), $2, srcspan $1 $>) }

QualVarSlice :: { ((QualName Name, SrcLoc), UncheckedSlice, SrcLoc) }
              : VarSlice
                { let ((v, vloc), y, loc) = $1 in ((qualName v, vloc), y, loc) }
              | 'qid[' DimIndices ']'
                { let L vloc (QUALINDEXING qs v) = $1
                  in ((QualName qs v, vloc), $2, srcspan $1 $>) }

DimIndex :: { UncheckedDimIndex }
         : Exp2                   { DimFix $1 }
         | Exp2 ':' Exp2          { DimSlice (Just $1) (Just $3) Nothing }
         | Exp2 ':'               { DimSlice (Just $1) Nothing Nothing }
         |      ':' Exp2          { DimSlice Nothing (Just $2) Nothing }
         |      ':'               { DimSlice Nothing Nothing Nothing }
         | Exp2 ':' Exp2 ':' Exp2 { DimSlice (Just $1) (Just $3) (Just $5) }
         |      ':' Exp2 ':' Exp2 { DimSlice Nothing (Just $2) (Just $4) }
         | Exp2 ':'      ':' Exp2 { DimSlice (Just $1) Nothing (Just $4) }
         |      ':'      ':' Exp2 { DimSlice Nothing Nothing (Just $3) }

DimIndices :: { [UncheckedDimIndex] }
            :             { [] }
            | DimIndices1 { fst $1 : snd $1 }

DimIndices1 :: { (UncheckedDimIndex, [UncheckedDimIndex]) }
             : DimIndex                 { ($1, []) }
             | DimIndex ',' DimIndices1 { ($1, fst $3 : snd $3) }

VarId :: { IdentBase NoInfo Name }
VarId : id { let L loc (ID name) = $1 in Ident name NoInfo loc }

FieldId :: { (Name, SrcLoc) }
         : id     { let L loc (ID name) = $1 in (name, loc) }
         | intlit { let L loc (INTLIT n) = $1 in (nameFromString (show n), loc) }

Pattern :: { PatternBase NoInfo Name }
Pattern : InnerPattern ':' TypeExpDecl { PatternAscription $1 $3 (srcspan $1 $>) }
        | InnerPattern                 { $1 }

Patterns1 :: { [PatternBase NoInfo Name] }
           : Pattern               { [$1] }
           | Pattern ',' Patterns1 { $1 : $3 }

InnerPattern :: { PatternBase NoInfo Name }
InnerPattern : id                               { let L loc (ID name) = $1 in Id name NoInfo loc }
             | '(' BindingBinOp ')'             { Id $2 NoInfo (srcspan $1 $>) }
             | '(' BindingUnOp ')'              { Id $2 NoInfo (srcspan $1 $>) }
             | '_'                              { Wildcard NoInfo $1 }
             | '(' ')'                          { TuplePattern [] (srcspan $1 $>) }
             | '(' Pattern ')'                  { PatternParens $2 (srcspan $1 $>) }
             | '(' Pattern ',' Patterns1 ')'    { TuplePattern ($2:$4) (srcspan $1 $>) }
             | '{' FieldPatterns '}'            { RecordPattern $2 (srcspan $1 $>) }

FieldPattern :: { (Name, PatternBase NoInfo Name) }
              : FieldId '=' Pattern
                { (fst $1, $3) }
              | FieldId ':' TypeExpDecl
                { (fst $1, PatternAscription (Id (fst $1) NoInfo (snd $1)) $3 (srcspan (snd $1) $>)) }
              | FieldId
                { (fst $1, Id (fst $1) NoInfo (snd $1)) }

FieldPatterns :: { [(Name, PatternBase NoInfo Name)] }
               : FieldPatterns1 { $1 }
               |                { [] }

FieldPatterns1 :: { [(Name, PatternBase NoInfo Name)] }
               : FieldPattern ',' FieldPatterns1 { $1 : $3 }
               | FieldPattern                    { [$1] }


maybeAscription(p) : ':' p { Just $2 }
                   |       { Nothing }

AttrInfo :: { AttrInfo }
         : id { let L _ (ID s) = $1 in AttrAtom s }
         | id '('       ')' { let L _ (ID s) = $1 in AttrComp s [] }
         | id '(' Attrs ')' { let L _ (ID s) = $1 in AttrComp s $3 }

Attrs :: { [AttrInfo] }
       : AttrInfo           { [$1] }
       | AttrInfo ',' Attrs { $1 : $3 }

Value :: { Value }
Value : IntValue { $1 }
      | FloatValue { $1 }
      | StringValue { $1 }
      | BoolValue { $1 }
      | ArrayValue { $1 }

CatValues :: { [Value] }
CatValues : Value CatValues { $1 : $2 }
          |                 { [] }

PrimType :: { PrimType }
         : id {% let L loc (ID s) = $1 in primTypeFromName loc s }

IntValue :: { Value }
         : SignedLit { PrimValue (SignedValue (fst $1)) }
         | '-' SignedLit { PrimValue (SignedValue (intNegate (fst $2))) }
         | UnsignedLit { PrimValue (UnsignedValue (fst $1)) }

FloatValue :: { Value }
         : FloatLit     { PrimValue (FloatValue (fst $1)) }
         | '-' FloatLit { PrimValue (FloatValue (floatNegate (fst $2))) }

StringValue :: { Value }
StringValue : stringlit  { let L pos (STRINGLIT s) = $1 in
                           ArrayValue (arrayFromList $ map (PrimValue . UnsignedValue . Int8Value . fromIntegral) $ encode s) $ Scalar $ Prim $ Signed Int32 }

BoolValue :: { Value }
BoolValue : true           { PrimValue $ BoolValue True }
          | false          { PrimValue $ BoolValue False }

SignedLit :: { (IntValue, SrcLoc) }
          : i8lit   { let L loc (I8LIT num)  = $1 in (Int8Value num, loc) }
          | i16lit  { let L loc (I16LIT num) = $1 in (Int16Value num, loc) }
          | i32lit  { let L loc (I32LIT num) = $1 in (Int32Value num, loc) }
          | i64lit  { let L loc (I64LIT num) = $1 in (Int64Value num, loc) }
          | intlit  { let L loc (INTLIT num) = $1 in (Int32Value $ fromInteger num, loc) }
          | charlit { let L loc (CHARLIT char) = $1 in (Int32Value $ fromIntegral $ ord char, loc) }

UnsignedLit :: { (IntValue, SrcLoc) }
            : u8lit  { let L pos (U8LIT num)  = $1 in (Int8Value $ fromIntegral num, pos) }
            | u16lit { let L pos (U16LIT num) = $1 in (Int16Value $ fromIntegral num, pos) }
            | u32lit { let L pos (U32LIT num) = $1 in (Int32Value $ fromIntegral num, pos) }
            | u64lit { let L pos (U64LIT num) = $1 in (Int64Value $ fromIntegral num, pos) }

FloatLit :: { (FloatValue, SrcLoc) }
         : f32lit { let L loc (F32LIT num) = $1 in (Float32Value num, loc) }
         | f64lit { let L loc (F64LIT num) = $1 in (Float64Value num, loc) }
         | QualName {% let (qn, loc) = $1 in
                       case qn of
                         QualName ["f32"] "inf" -> return (Float32Value (1/0), loc)
                         QualName ["f32"] "nan" -> return (Float32Value (0/0), loc)
                         QualName ["f64"] "inf" -> return (Float64Value (1/0), loc)
                         QualName ["f64"] "nan" -> return (Float64Value (0/0), loc)
                         _ -> parseErrorAt (snd $1) Nothing
                    }
         | floatlit { let L loc (FLOATLIT num) = $1 in (Float64Value num, loc) }

ArrayValue :: { Value }
ArrayValue :  '[' Value ']'
             {% return $ ArrayValue (arrayFromList [$2]) $
                arrayOf (valueType $2) (ShapeDecl [1]) Unique
             }
           |  '[' Value ',' Values ']'
             {% case combArrayElements $2 $4 of
                  Left e -> throwError e
                  Right v -> return $ ArrayValue (arrayFromList $ $2:$4) $
                             arrayOf (valueType v) (ShapeDecl [1+fromIntegral (length $4)]) Unique
             }
           | id '(' ValueType ')'
             {% ($1 `mustBe` "empty") >> mustBeEmpty (srcspan $2 $4) $3 >> return (ArrayValue (listArray (0,-1) []) $3) }

           -- Errors
           | '[' ']'
             {% emptyArrayError $1 }

Dim :: { Int64 }
Dim : intlit { let L _ (INTLIT num) = $1 in fromInteger num }

ValueType :: { ValueType }
ValueType : '[' Dim ']' ValueType  { arrayOf $4 (ShapeDecl [$2]) Nonunique }
          | '[' Dim ']' PrimType { arrayOf (Scalar (Prim $4)) (ShapeDecl [$2]) Nonunique }

Values :: { [Value] }
Values : Value ',' Values { $1 : $3 }
       | Value            { [$1] }
       |                  { [] }

{

addDoc :: DocComment -> UncheckedDec -> UncheckedDec
addDoc doc (ValDec val) = ValDec (val { valBindDoc = Just doc })
addDoc doc (TypeDec tp) = TypeDec (tp { typeDoc = Just doc })
addDoc doc (SigDec sig) = SigDec (sig { sigDoc = Just doc })
addDoc doc (ModDec mod) = ModDec (mod { modDoc = Just doc })
addDoc _ dec = dec

addDocSpec :: DocComment -> SpecBase NoInfo Name -> SpecBase NoInfo Name
addDocSpec doc (TypeAbbrSpec tpsig) = TypeAbbrSpec (tpsig { typeDoc = Just doc })
addDocSpec doc val@(ValSpec {}) = val { specDoc = Just doc }
addDocSpec doc (TypeSpec l name ps _ loc) = TypeSpec l name ps (Just doc) loc
addDocSpec doc (ModSpec name se _ loc) = ModSpec name se (Just doc) loc
addDocSpec _ spec = spec

addAttr :: AttrInfo -> UncheckedDec -> UncheckedDec
addAttr attr (ValDec val) =
  ValDec $ val { valBindAttrs = attr : valBindAttrs val }
addAttr attr dec =
  dec

-- We will extend this function once we actually start tracking these.
addAttrSpec :: AttrInfo -> UncheckedSpec -> UncheckedSpec
addAttrSpec _attr dec = dec

reverseNonempty :: (a, [a]) -> (a, [a])
reverseNonempty (x, l) =
  case reverse (x:l) of
    x':rest -> (x', rest)
    []      -> (x, [])

mustBe (L loc (ID got)) expected
  | nameToString got == expected = return ()
mustBe (L loc _) expected =
  parseErrorAt loc $ Just $
  "Only the keyword '" ++ expected ++ "' may appear here."

mustBeEmpty :: SrcLoc -> ValueType -> ParserMonad ()
mustBeEmpty loc (Array _ _ _ (ShapeDecl dims))
  | any (==0) dims = return ()
mustBeEmpty loc t =
  parseErrorAt loc $ Just $ pretty t ++ " is not an empty array."

data ParserEnv = ParserEnv {
                 parserFile :: FilePath
               }

type ParserMonad a =
  ExceptT String (
    StateT ParserEnv (
       StateT ([L Token], Pos) ReadLineMonad)) a

data ReadLineMonad a = Value a
                     | GetLine (Maybe T.Text -> ReadLineMonad a)

readLineFromMonad :: ReadLineMonad (Maybe T.Text)
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

getLinesFromM :: Monad m => m T.Text -> ReadLineMonad a -> m a
getLinesFromM _ (Value x) = return x
getLinesFromM fetch (GetLine f) = do
  s <- fetch
  getLinesFromM fetch $ f $ Just s

getLinesFromTexts :: [T.Text] -> ReadLineMonad a -> Either String a
getLinesFromTexts _ (Value x) = Right x
getLinesFromTexts (x : xs) (GetLine f) = getLinesFromTexts xs $ f $ Just x
getLinesFromTexts [] (GetLine f) = getLinesFromTexts [] $ f Nothing

getNoLines :: ReadLineMonad a -> Either String a
getNoLines (Value x) = Right x
getNoLines (GetLine f) = getNoLines $ f Nothing

combArrayElements :: Value
                  -> [Value]
                  -> Either String Value
combArrayElements t ts = foldM comb t ts
  where comb x y
          | valueType x == valueType y = Right x
          | otherwise                  = Left $ "Elements " ++ pretty x ++ " and " ++
                                         pretty y ++ " cannot exist in same array."

arrayFromList :: [a] -> Array Int a
arrayFromList l = listArray (0, length l-1) l

applyExp :: [UncheckedExp] -> ParserMonad UncheckedExp
applyExp all@((Constr n [] _ loc1):es) =
  return $ Constr n es NoInfo (srcspan loc1 (last all))
applyExp es =
  foldM ap (head es) (tail es)
  where
     ap (AppExp (Index e is floc) _) (ArrayLit xs _ xloc) =
       parseErrorAt (srcspan floc xloc) $
       Just $ pretty $ "Incorrect syntax for multi-dimensional indexing." </>
       "Use" <+> align (ppr index)
       where index = AppExp (Index e (is++map DimFix xs) xloc) NoInfo
     ap f x =
        return $ AppExp (Apply f x NoInfo (srcspan f x)) NoInfo

patternExp :: UncheckedPattern -> ParserMonad UncheckedExp
patternExp (Id v _ loc) = return $ Var (qualName v) NoInfo loc
patternExp (TuplePattern pats loc) = TupLit <$> (mapM patternExp pats) <*> return loc
patternExp (Wildcard _ loc) = parseErrorAt loc $ Just "cannot have wildcard here."
patternExp (PatternAscription pat _ _) = patternExp pat
patternExp (PatternParens pat _) = patternExp pat
patternExp (RecordPattern fs loc) = RecordLit <$> mapM field fs <*> pure loc
  where field (name, pat) = RecordFieldExplicit name <$> patternExp pat <*> pure loc

eof :: Pos -> L Token
eof pos = L (SrcLoc $ Loc pos pos) EOF

binOpName (L loc (SYMBOL _ qs op)) = (QualName qs op, loc)

binOp x (L loc (SYMBOL _ qs op)) y =
  AppExp (BinOp (QualName qs op, loc) NoInfo (x, NoInfo) (y, NoInfo) (srcspan x y)) NoInfo

getTokens :: ParserMonad ([L Token], Pos)
getTokens = lift $ lift get

putTokens :: ([L Token], Pos) -> ParserMonad ()
putTokens = lift . lift . put

primTypeFromName :: SrcLoc -> Name -> ParserMonad PrimType
primTypeFromName loc s = maybe boom return $ M.lookup s namesToPrimTypes
  where boom = parseErrorAt loc $ Just $ "No type named " ++ nameToString s

getFilename :: ParserMonad FilePath
getFilename = lift $ gets parserFile

intNegate :: IntValue -> IntValue
intNegate (Int8Value v) = Int8Value (-v)
intNegate (Int16Value v) = Int16Value (-v)
intNegate (Int32Value v) = Int32Value (-v)
intNegate (Int64Value v) = Int64Value (-v)

floatNegate :: FloatValue -> FloatValue
floatNegate (Float32Value v) = Float32Value (-v)
floatNegate (Float64Value v) = Float64Value (-v)

readLine :: ParserMonad (Maybe T.Text)
readLine = lift $ lift $ lift readLineFromMonad

lexer :: (L Token -> ParserMonad a) -> ParserMonad a
lexer cont = do
  (ts, pos) <- getTokens
  case ts of
    [] -> do
      ended <- lift $ runExceptT $ cont $ eof pos
      case ended of
        Right x -> return x
        Left parse_e -> do
          line <- readLine
          ts' <-
            case line of Nothing -> throwError parse_e
                         Just line' -> return $ scanTokensText (advancePos pos '\n') line'
          (ts'', pos') <-
            case ts' of Right x -> return x
                        Left lex_e  -> throwError lex_e
          case ts'' of
            [] -> cont $ eof pos
            xs -> do
              putTokens (xs, pos')
              lexer cont
    (x : xs) -> do
      putTokens (xs, pos)
      cont x

parseError :: L Token -> ParserMonad a
parseError (L loc EOF) =
  parseErrorAt (srclocOf loc) $ Just "unexpected end of file."
parseError (L loc DOC{}) =
  parseErrorAt (srclocOf loc) $
  Just "documentation comments ('-- |') are only permitted when preceding declarations."
parseError tok = parseErrorAt (srclocOf tok) Nothing

parseErrorAt :: SrcLoc -> Maybe String -> ParserMonad a
parseErrorAt loc Nothing = throwError $ "Error at " ++ locStr loc ++ ": Parse error."
parseErrorAt loc (Just s) = throwError $ "Error at " ++ locStr loc ++ ": " ++ s

emptyArrayError :: SrcLoc -> ParserMonad a
emptyArrayError loc =
  parseErrorAt loc $
  Just "write empty arrays as 'empty(t)', for element type 't'.\n"

twoDotsRange :: SrcLoc -> ParserMonad a
twoDotsRange loc = parseErrorAt loc $ Just "use '...' for ranges, not '..'.\n"

--- Now for the parser interface.

-- | A parse error.  Use 'show' to get a human-readable description.
data ParseError = ParseError String

instance Show ParseError where
  show (ParseError s) = s

parseInMonad :: ParserMonad a -> FilePath -> T.Text
             -> ReadLineMonad (Either ParseError a)
parseInMonad p file program =
  either (Left . ParseError) Right <$> either (return . Left)
  (evalStateT (evalStateT (runExceptT p) env))
  (scanTokensText (Pos file 1 1 0) program)
  where env = ParserEnv file

parseIncremental :: ParserMonad a -> FilePath -> T.Text
                 -> Either ParseError a
parseIncremental p file program =
  either (Left . ParseError) id
  $ getLinesFromTexts (T.lines program)
  $ parseInMonad p file mempty

parse :: ParserMonad a -> FilePath -> T.Text
      -> Either ParseError a
parse p file program =
  either (Left . ParseError) id
  $ getNoLines $ parseInMonad p file program

-- | Parse an Futhark expression incrementally from monadic actions, using the
-- 'FilePath' as the source name for error messages.
parseExpIncrM :: Monad m =>
                 m T.Text -> FilePath -> T.Text
              -> m (Either ParseError UncheckedExp)
parseExpIncrM fetch file program =
  getLinesFromM fetch $ parseInMonad expression file program

-- | Parse either an expression or a declaration incrementally;
-- favouring declarations in case of ambiguity.
parseDecOrExpIncrM :: Monad m =>
                      m T.Text -> FilePath -> T.Text
                   -> m (Either ParseError (Either UncheckedDec UncheckedExp))
parseDecOrExpIncrM fetch file input =
  case parseInMonad declaration file input of
    Value Left{} -> fmap Right <$> parseExpIncrM fetch file input
    Value (Right d) -> return $ Right $ Left d
    GetLine c -> do
      l <- fetch
      parseDecOrExpIncrM fetch file $ input <> "\n" <> l
}
