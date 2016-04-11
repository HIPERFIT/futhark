{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
-- | This module implements an optimisation that moves in-place
-- updates into/before loops where possible, with the end goal of
-- minimising memory copies.  As an example, consider this program:
--
-- @
--   loop (r = r0) = for i < n do
--     let a = r[i] in
--     let r[i] = a * i in
--     r
--     in
--   ...
--   let x = y with [k] <- r in
--   ...
-- @
--
-- We want to turn this into the following:
--
-- @
--   let x0 = y with [k] <- r0
--   loop (x = x0) = for i < n do
--     let a = a[k,i] in
--     let x[k,i] = a * i in
--     x
--     in
--   let r = x[y] in
--   ...
-- @
--
-- The intent is that we are also going to optimise the new data
-- movement (in the @x0@-binding), possibly by changing how @r0@ is
-- defined.  For the above transformation to be valid, a number of
-- conditions must be fulfilled:
--
--    (1) @r@ must not be consumed after the original in-place update.
--
--    (2) @k@ and @y@ must be available at the beginning of the loop.
--
--    (3) @x@ must be visible whenever @r@ is visible.  (This means
--    that both @x@ and @r@ must be bound in the same 'Body'.)
--
--    (4) If @x@ is consumed at a point after the loop, @r@ must not
--    be used after that point.
--
--    (5) The size of @r@ is invariant inside the loop.
--
--    (6) The value @r@ must come from something that we can actually
--    optimise (e.g. not a function parameter).
--
--    (7) @y@ (or its aliases) may not be used inside the body of the
--    loop.
--
-- FIXME: the implementation is not finished yet.  Specifically, the
-- above conditions are not really checked.
module Futhark.Optimise.InPlaceLowering
       (
         inPlaceLowering
       ) where

import Control.Applicative
import Control.Monad.RWS hiding (mapM_)
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.Foldable
import Data.Maybe

import Futhark.Analysis.Alias
import Futhark.Representation.Aliases
import Futhark.Representation.Kernels (Kernels)
import Futhark.Representation.Kernels.Kernel
import Futhark.Optimise.InPlaceLowering.LowerIntoBinding
import Futhark.MonadFreshNames
import Futhark.Binder
import Futhark.Pass
import Futhark.Tools (intraproceduralTransformation)

import Prelude hiding (any, mapM_, elem, all)

-- | Apply the in-place lowering optimisation to the given program.
inPlaceLowering :: Pass Kernels Kernels
inPlaceLowering = simplePass
                  "In-place lowering"
                  "Lower in-place updates into loops" $
                  fmap removeProgAliases .
                  intraproceduralTransformation optimiseFunDef .
                  aliasAnalysis

optimiseFunDef :: MonadFreshNames m => FunDef Kernels -> m (FunDef Kernels)
optimiseFunDef fundec =
  modifyNameSource $ runForwardingM $
  bindingFParams (funDefParams fundec) $ do
    body <- optimiseBody $ funDefBody fundec
    return $ fundec { funDefBody = body }

optimiseBody :: Body Kernels -> ForwardingM (Body Kernels)
optimiseBody (Body als bnds res) = do
  bnds' <- deepen $ optimiseBindings bnds $
    mapM_ seen res
  return $ Body als bnds' res
  where seen Constant{} = return ()
        seen (Var v)    = seenVar v

optimiseBindings :: [Binding Kernels]
                 -> ForwardingM ()
                 -> ForwardingM [Binding Kernels]
optimiseBindings [] m = m >> return []

optimiseBindings (bnd:bnds) m = do
  (bnds', bup) <- tapBottomUp $ bindingBinding bnd $ optimiseBindings bnds m
  bnd' <- optimiseInBinding bnd
  case filter ((`elem` boundHere) . updateValue) $
       forwardThese bup of
    [] -> checkIfForwardableUpdate bnd' bnds'
    updates -> do
      let updateBindings = map updateBinding updates
      -- Condition (5) and (7) are assumed to be checked by
      -- lowerUpdate.
      case lowerUpdate (removeBindingAliases bnd') $ map (fmap snd) updates of
        Just lowering -> do new_bnds <- map analyseBinding <$> lowering
                            new_bnds' <- optimiseBindings new_bnds $
                                         tell bup { forwardThese = [] }
                            return $ new_bnds' ++ bnds'
        Nothing       -> checkIfForwardableUpdate bnd' $
                         updateBindings ++ bnds'

  where boundHere = patternNames $ bindingPattern bnd

        checkIfForwardableUpdate bnd'@(Let pat _ e) bnds'
            | [PatElem v (BindInPlace cs src [i]) attr] <- patternElements pat,
              PrimOp (SubExp (Var ve)) <- e = do
                forwarded <- maybeForward ve v attr cs src i
                return $ if forwarded
                         then bnds'
                         else bnd' : bnds'
        checkIfForwardableUpdate bnd' bnds' =
          return $ bnd' : bnds'

optimiseInBinding :: Binding Kernels
                  -> ForwardingM (Binding Kernels)
optimiseInBinding (Let pat attr e) = do
  e' <- optimiseExp e
  return $ Let pat attr e'

optimiseExp :: Exp Kernels -> ForwardingM (Exp Kernels)
optimiseExp (DoLoop ctx val form body) =
  bindingIndices (boundInForm form) $
  bindingFParams (map fst $ ctx ++ val) $ do
    body' <- optimiseBody body
    return $ DoLoop ctx val form body'
  where boundInForm (ForLoop i _) = [i]
        boundInForm (WhileLoop _) = []
optimiseExp (Op (MapKernel cs w index ispace inps returns body)) =
  bindingIndices (index : map fst ispace) $
  bindingLParams (map kernelInputParam inps) $ do
    body' <- optimiseBody body
    return $ Op $ MapKernel cs w index ispace inps returns body'
optimiseExp e = mapExpM optimise e
  where optimise = identityMapper { mapOnBody = optimiseBody
                                  }

data Entry = Entry { entryNumber :: Int
                   , entryAliases :: Names
                   , entryDepth :: Int
                   , entryOptimisable :: Bool
                   , entryType :: NameInfo (Aliases Kernels)
                   }

type VTable = HM.HashMap VName Entry

data TopDown = TopDown { topDownCounter :: Int
                       , topDownTable :: VTable
                       , topDownDepth :: Int
                       }

data BottomUp = BottomUp { bottomUpSeen :: Names
                         , forwardThese :: [DesiredUpdate (LetAttr (Aliases Kernels))]
                         }

instance Monoid BottomUp where
  BottomUp seen1 forward1 `mappend` BottomUp seen2 forward2 =
    BottomUp (seen1 `mappend` seen2) (forward1 `mappend` forward2)
  mempty = BottomUp mempty mempty

updateBinding :: DesiredUpdate (LetAttr (Aliases Kernels)) -> Binding Kernels
updateBinding fwd =
  mkLet [] [(Ident (updateName fwd) $ typeOf $ updateType fwd,
             BindInPlace
             (updateCertificates fwd)
             (updateSource fwd)
             (updateIndices fwd))] $
  PrimOp $ SubExp $ Var $ updateValue fwd

newtype ForwardingM a = ForwardingM (RWS TopDown BottomUp VNameSource a)
                      deriving (Monad, Applicative, Functor,
                                MonadReader TopDown,
                                MonadWriter BottomUp,
                                MonadState VNameSource)

instance MonadFreshNames ForwardingM where
  getNameSource = get
  putNameSource = put

instance HasScope (Aliases Kernels) ForwardingM where
  askScope = HM.map entryType <$> asks topDownTable

runForwardingM :: ForwardingM a -> VNameSource -> (a, VNameSource)
runForwardingM (ForwardingM m) src = let (x, src', _) = runRWS m emptyTopDown src
                                     in (x, src')
  where emptyTopDown = TopDown { topDownCounter = 0
                               , topDownTable = HM.empty
                               , topDownDepth = 0
                               }

bindingParams :: (attr -> NameInfo (Aliases Kernels))
              -> [Param attr]
               -> ForwardingM a
               -> ForwardingM a
bindingParams f params = local $ \(TopDown n vtable d) ->
  let entry fparam =
        (paramName fparam,
         Entry n mempty d False $ f $ paramAttr fparam)
      entries = HM.fromList $ map entry params
  in TopDown (n+1) (HM.union entries vtable) d

bindingFParams :: [FParam (Aliases Kernels)]
               -> ForwardingM a
               -> ForwardingM a
bindingFParams = bindingParams FParamInfo

bindingLParams :: [LParam (Aliases Kernels)]
               -> ForwardingM a
               -> ForwardingM a
bindingLParams = bindingParams LParamInfo

bindingBinding :: Binding Kernels
               -> ForwardingM a
               -> ForwardingM a
bindingBinding (Let pat _ _) = local $ \(TopDown n vtable d) ->
  let entries = HM.fromList $ map entry $ patternElements pat
      entry patElem =
        let (aliases, _) = patElemAttr patElem
        in (patElemName patElem,
            Entry n (unNames aliases) d True $ LetInfo $ patElemAttr patElem)
  in TopDown (n+1) (HM.union entries vtable) d

bindingIndices :: [VName]
               -> ForwardingM a
               -> ForwardingM a
bindingIndices is = local $ \(TopDown n vtable d) ->
  let entries = HM.fromList $ map entry is
      entry v =
        (v,
         Entry n mempty d False IndexInfo)
  in TopDown (n+1) (HM.union entries vtable) d

bindingNumber :: VName -> ForwardingM Int
bindingNumber name = do
  res <- asks $ fmap entryNumber . HM.lookup name . topDownTable
  case res of Just n  -> return n
              Nothing -> fail $ "bindingNumber: variable " ++
                         pretty name ++ " not found."

deepen :: ForwardingM a -> ForwardingM a
deepen = local $ \env -> env { topDownDepth = topDownDepth env + 1 }

areAvailableBefore :: [SubExp] -> VName -> ForwardingM Bool
areAvailableBefore ses point = do
  pointN <- bindingNumber point
  nameNs <- mapM bindingNumber names
  return $ all (< pointN) nameNs
  where names = mapMaybe isVar ses
        isVar (Var v)    = Just v
        isVar Constant{} = Nothing

isInCurrentBody :: VName -> ForwardingM Bool
isInCurrentBody name = do
  current <- asks topDownDepth
  res <- asks $ fmap entryDepth . HM.lookup name . topDownTable
  case res of Just d  -> return $ d == current
              Nothing -> fail $ "isInCurrentBody: variable " ++
                         pretty name ++ " not found."

isOptimisable :: VName -> ForwardingM Bool
isOptimisable name = do
  res <- asks $ fmap entryOptimisable . HM.lookup name . topDownTable
  case res of Just b  -> return b
              Nothing -> fail $ "isOptimisable: variable " ++
                         pretty name ++ " not found."

seenVar :: VName -> ForwardingM ()
seenVar name = do
  aliases <- asks $
             maybe mempty entryAliases .
             HM.lookup name . topDownTable
  tell $ mempty { bottomUpSeen = HS.insert name aliases }

tapBottomUp :: ForwardingM a -> ForwardingM (a, BottomUp)
tapBottomUp m = do (x,bup) <- listen m
                   return (x, bup)

maybeForward :: VName
             -> VName -> LetAttr (Aliases Kernels) -> Certificates -> VName -> SubExp
             -> ForwardingM Bool
maybeForward v dest_nm dest_attr cs src i = do
  -- Checks condition (2)
  available <- [i,Var src] `areAvailableBefore` v
  -- ...subcondition, the certificates must also.
  certs_available <- map Var cs `areAvailableBefore` v
  -- Check condition (3)
  samebody <- isInCurrentBody v
  -- Check condition (6)
  optimisable <- isOptimisable v
  not_prim <- not <$> primType <$> lookupType v
  if available && certs_available && samebody && optimisable && not_prim then do
    let fwd = DesiredUpdate dest_nm dest_attr cs src [i] v
    tell mempty { forwardThese = [fwd] }
    return True
    else return False
