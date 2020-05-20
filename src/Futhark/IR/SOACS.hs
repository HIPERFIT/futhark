{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE FlexibleInstances #-}
-- | A simple representation with SOACs and nested parallelism.
module Futhark.IR.SOACS
       ( -- * The Lore definition
         SOACS
         -- * Syntax types
       , Body
       , Stm
       , Pattern
       , Exp
       , Lambda
       , FParam
       , LParam
       , RetType
       , PatElem
         -- * Module re-exports
       , module Futhark.IR.Prop
       , module Futhark.IR.Traversals
       , module Futhark.IR.Pretty
       , module Futhark.IR.Syntax
       , module Futhark.IR.SOACS.SOAC
       , AST.LambdaT(Lambda)
       , AST.BodyT(Body)
       , AST.PatternT(Pattern)
       , AST.PatElemT(PatElem)
       )
where

import qualified Futhark.IR.Syntax as AST
import Futhark.IR.Syntax
  hiding (Exp, Body, Stm,
          Pattern, Lambda, FParam, LParam, RetType, PatElem)
import Futhark.IR.SOACS.SOAC
import Futhark.IR.Prop
import Futhark.IR.Traversals
import Futhark.IR.Pretty
import Futhark.Binder
import Futhark.Construct
import qualified Futhark.TypeCheck as TypeCheck

-- This module could be written much nicer if Haskell had functors
-- like Standard ML.  Instead, we have to abuse the namespace/module
-- system.

-- | The lore for the basic representation.
data SOACS

instance Decorations SOACS where
  type Op SOACS = SOAC SOACS

instance ASTLore SOACS where
  expTypesFromPattern = return . expExtTypesFromPattern

type Exp = AST.Exp SOACS
type Body = AST.Body SOACS
type Stm = AST.Stm SOACS
type Pattern = AST.Pattern SOACS
type Lambda = AST.Lambda SOACS
type FParam = AST.FParam SOACS
type LParam = AST.LParam SOACS
type RetType = AST.RetType SOACS
type PatElem = AST.PatElem SOACS

instance TypeCheck.CheckableOp SOACS where
  checkOp = typeCheckSOAC

instance TypeCheck.Checkable SOACS where

instance Bindable SOACS where
  mkBody = AST.Body ()
  mkExpPat ctx val _ = basicPattern ctx val
  mkExpDec _ _ = ()
  mkLetNames = simpleMkLetNames

instance BinderOps SOACS where
  mkExpDecB = bindableMkExpDecB
  mkBodyB = bindableMkBodyB
  mkLetNamesB = bindableMkLetNamesB

instance PrettyLore SOACS where
