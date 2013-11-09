{-# LANGUAGE GeneralizedNewtypeDeriving #-}
-- |
--
-- Perform simple hoisting of let-bindings, moving them out as far as
-- possible (particularly outside loops).
--
module L0C.EnablingOpts.Hoisting
  ( transformProg )
  where

import Control.Applicative
import Control.Arrow (first)
import Control.Monad.Writer
import Control.Monad.Reader
import Control.Monad.State
import Control.Monad.RWS

import Data.Graph
import Data.List
import Data.Loc
import Data.Maybe
import qualified Data.Map as M
import Data.Ord
import qualified Data.Set as S

import L0C.L0
import L0C.Substitute
import L0C.FreshNames

data BindNeed = LoopBind TupIdent Exp Ident Exp Exp
              | LetBind TupIdent Exp [(TupIdent, Exp)]
              | LetWithBind Certificates Ident Ident [Exp] Exp
                deriving (Show, Eq, Ord)

type NeedSet = S.Set BindNeed

asTail :: BindNeed -> Exp
asTail (LoopBind mergepat mergeexp i bound loopbody) =
  DoLoop mergepat mergeexp i bound loopbody (TupLit [] loc) loc
    where loc = srclocOf mergepat
asTail (LetBind pat e _) =
  LetPat pat e (TupLit [] loc) loc
    where loc = srclocOf pat
asTail (LetWithBind cs dest src is ve) =
  LetWith cs dest src is ve (Var dest) $ srclocOf dest

requires :: BindNeed -> S.Set VName
requires (LetBind pat e ((altpat,alte):alts)) =
  requires (LetBind pat e []) <> requires (LetBind altpat alte alts)
requires bnd = S.map identName $ freeInExp $ asTail bnd

provides :: BindNeed -> S.Set VName
provides (LoopBind mergepat _ _ _ _) = patNames mergepat
provides (LetBind pat _ _) = patNames pat
provides (LetWithBind _ dest _ _ _) = S.singleton $ identName dest

data Need = Need { needBindings :: NeedSet
                 }

instance Monoid Need where
  Need b1 `mappend` Need b2 = Need $ b1 <> b2
  mempty = Need S.empty

type ColExps = [Exp]

data ShapeBinding = DimSizes [ColExps]
                    deriving (Show, Eq)

instance Monoid ShapeBinding where
  mempty = DimSizes []
  DimSizes xs `mappend` DimSizes ys = DimSizes $ xs ++ ys

type ShapeMap = M.Map Ident ShapeBinding

data Env = Env { envBindings :: ShapeMap
               }

emptyEnv :: Env
emptyEnv = Env {
             envBindings = M.empty
           }

varExp :: Exp -> Maybe Ident
varExp (Var k) = Just k
varExp _       = Nothing

vars :: [Exp] -> [Ident]
vars = mapMaybe varExp

isArrayIdent :: Ident -> Bool
isArrayIdent idd = case identType idd of
                     Array {} -> True
                     _        -> False

lookupShapeBindings :: Ident -> ShapeMap -> [ColExps]
lookupShapeBindings idd m = delve S.empty idd
  where
    delve s k | k `S.member` s = blank k
              | otherwise =
                case M.lookup k m of
                  Nothing -> blank k
                  Just (DimSizes colexps) ->
                    map (concatMap (recurse $ k `S.insert` s)) colexps

    blank k = replicate (arrayDims $ identType k) []

    recurse s e@(Size _ i (Var k') _) =
      case drop i $ delve s k' of
        (d:ds):_ -> d:ds
        _        -> [e]
    recurse _ _ = []

newtype HoistM a = HoistM (RWS
                           Env                -- Reader
                           Need               -- Writer
                           (NameSource VName) -- State
                           a)
  deriving (Applicative, Functor, Monad,
            MonadWriter Need, MonadReader Env, MonadState (NameSource VName))

runHoistM :: HoistM a -> NameSource VName -> a
runHoistM (HoistM m) src = let (x, _, _) = runRWS m emptyEnv src
                           in x

new :: String -> HoistM VName
new k = do (name, src) <- gets $ flip newVName k
           put src
           return name

addNewBinding :: String -> Exp -> HoistM Ident
addNewBinding k e = do
  k' <- new k
  let ident = Ident { identName = k'
                    , identType = typeOf e
                    , identSrcLoc = srclocOf e }
  addBinding (Id ident) e
  return ident

addBinding :: TupIdent -> Exp -> HoistM ()
addBinding pat e@(Size _ i (Var x) _) = do
  let mkAlt es = case drop i es of
                   des:_ -> [(pat, des)]
                   _     -> []
  alts <- concatMap mkAlt <$> asks (lookupShapeBindings x . envBindings)
  addSeveralBindings pat e alts

addBinding pat e = addSingleBinding pat e

addSingleBinding :: TupIdent -> Exp -> HoistM ()
addSingleBinding pat e = addSeveralBindings pat e []

addSeveralBindings :: TupIdent -> Exp -> [(TupIdent, Exp)] -> HoistM ()
addSeveralBindings pat e alts =
  tell $ Need $ S.singleton $ LetBind pat e alts

bindLet :: TupIdent -> Exp -> HoistM a -> HoistM a
bindLet (Id dest) (Var src) m = do
  addBinding (Id dest) (Var src)
  case identType src of Array {} -> withShape dest (slice [] 0 src) m
                        _        -> m

bindLet pat@(Id dest) e@(Iota (Var x) _) m = do
  addBinding pat e
  withShape dest [Var x] m

bindLet pat@(Id dest) e@(Replicate (Var x) (Var y) _) m = do
  addBinding pat e
  withShape dest (Var x:slice [] 0 y) m

bindLet pat@(TupId [dest1, dest2] _) e@(Split cs (Var n) (Var src) _ loc) m = do
  addBinding pat e
  src_sz <- addNewBinding "split_src_sz" $ Size cs 0 (Var src) loc
  split_sz <- addNewBinding "split_sz" $
              BinOp Minus (Var src_sz) (Var n) (Elem Int) loc
  withShapes [(dest1, Var n : rest),
              (dest2, Var split_sz : rest)] m
    where rest = [ Size cs i (Var src) loc
                   | i <- [1.. arrayDims (identType src) - 1]]

bindLet pat@(Id dest) e@(Concat cs (Var x) (Var y) loc) m = do
  concat_x <- addNewBinding "concat_x" $ Size cs 0 (Var x) loc
  concat_y <- addNewBinding "concat_y" $ Size cs 0 (Var y) loc
  concat_sz <- addNewBinding "concat_sz" $
               BinOp Plus (Var concat_x) (Var concat_y) (Elem Int) loc
  withShape dest (Var concat_sz :
                  [Size cs i (Var x) loc | i <- [1..arrayDims (identType x) - 1]]
                 ) $ addBinding pat e >> m

bindLet pat e@(Map2 cs _ srcs _ _) m = do
  addBinding pat e
  withShapes (sameOuterShapes cs $ S.toList (patIdents pat) ++ vars srcs) m

bindLet pat e@(Reduce2 cs _ _ srcs _ _) m = do
  addBinding pat e
  withShapes (sameOuterShapesExps cs srcs) m

bindLet pat e@(Scan2 cs _ _ srcs _ _) m = do
  addBinding pat e
  withShapes (sameOuterShapesExps cs srcs) m

bindLet pat e@(Filter2 cs _ srcs _) m = do
  addBinding pat e
  withShapes (sameOuterShapesExps cs srcs) m

bindLet pat e@(Redomap2 cs _ _ _ srcs _ _) m = do
  addBinding pat e
  withShapes (sameOuterShapesExps cs srcs) m

bindLet pat@(Id dest) e@(Index cs src idxs _ _) m = do
  addBinding pat e
  withShape dest (slice cs (length idxs) src) m

bindLet pat@(Id dest) e@(Transpose cs k n (Var src) loc) m = do
  addBinding pat e
  withShape dest dims m
    where dims = transposeIndex k n
                 [Size cs i (Var src) loc
                  | i <- [0..arrayDims (identType src) - 1]]

bindLet pat e m = do
  addBinding pat e
  m

bindLetWith :: Certificates -> Ident -> Ident -> [Exp] -> Exp -> HoistM a -> HoistM a
bindLetWith cs dest src is ve m = do
  tell $ Need $ S.singleton $ LetWithBind cs dest src is ve
  withShape dest (slice [] 0 src) m

bindLoop :: TupIdent -> Exp -> Ident -> Exp -> Exp -> HoistM a -> HoistM a
bindLoop pat e i bound body m = do
  tell $ Need $ S.singleton $ LoopBind pat e i bound body
  m

slice :: Certificates -> Int -> Ident -> [Exp]
slice cs d k = [ Size cs i (Var k) $ srclocOf k
                 | i <- [d..arrayDims (identType k)-1]]

withShape :: Ident -> [Exp] -> HoistM a -> HoistM a
withShape dest src m = do
  bnds <- asks envBindings
  let srcs = map (inspect bnds) src
  local (\env -> env { envBindings =
                         M.insertWith (<>) dest (DimSizes srcs)
                            $ envBindings env }) m
    where inspect bnds (Size _ i (Var k) _)
            | (x:xs):_ <- drop i $ lookupShapeBindings k bnds = x:xs
          inspect _ e                                         = [e]

withShapes :: [(TupIdent, [Exp])] -> HoistM a -> HoistM a
withShapes [] m =
  m
withShapes ((Id dest, es):rest) m =
  withShape dest es $ withShapes rest m
withShapes (_:rest) m =
  withShapes rest m

sameOuterShapesExps :: Certificates -> [Exp] -> [(TupIdent, [Exp])]
sameOuterShapesExps cs = sameOuterShapes cs . vars

sameOuterShapes :: Certificates -> [Ident] -> [(TupIdent, [Exp])]
sameOuterShapes cs = outer' []
  where outer' _ [] = []
        outer' prev (k:ks) =
          [ (Id k, [Size cs 0 (Var k') $ srclocOf k])
            | k' <- prev ++ ks ] ++
          outer' (k:prev) ks

-- | Run the let-hoisting algorithm on the given program.  Even if the
-- output differs from the output, meaningful hoisting may not have
-- taken place - the order of bindings may simply have been
-- rearranged.  The function is idempotent, however.
transformProg :: Prog -> Prog
transformProg prog =
  Prog $ runHoistM (mapM transformFun $ progFunctions prog) namesrc
  where namesrc = newNameSourceForProg prog

transformFun :: FunDec -> HoistM FunDec
transformFun (fname, rettype, params, body, loc) = do
  body' <- blockAllHoisting $ hoistInExp body
  return (fname, rettype, params, body', loc)

-- The hoister is able to quite easily do CSE, so let's do that.  We
-- only need a few helper functions.

-- | Convert a pattern to an expression given the value returned by
-- that pattern.  Uses a 'Maybe' type as patterns using 'Wildcard's
-- cannot be thus converted.
patToExp :: TupIdent -> Maybe Exp
patToExp (Wildcard _ _)   = Nothing
patToExp (Id idd)         = Just $ Var idd
patToExp (TupId pats loc) = TupLit <$> mapM patToExp pats <*> pure loc

mkSubsts :: TupIdent -> Exp -> M.Map VName VName
mkSubsts pat e = execWriter $ subst pat e
  where subst (Id idd1) (Var idd2) =
          tell $ M.singleton (identName idd1) (identName idd2)
        subst (TupId pats _) (TupLit es _) =
          zipWithM_ subst pats es
        subst _ _ =
          return ()

type DupeState = (M.Map Exp Exp, M.Map VName VName)

newDupeState :: DupeState
newDupeState = (M.empty, M.empty)

-- | The main CSE function.  Given a state, a pattern and an
-- expression to be bound to that pattern, return a replacement
-- pattern (always the same as the input pattern, actually), a
-- replacement expression, and a new state.  The function will look in
-- the state to determine whether the expression can be replaced with
-- something bound previously.
handleDuplicates :: DupeState -> TupIdent -> Exp
                -> (TupIdent, Exp, DupeState)
-- Arrays may be consumed, so don't eliminate expressions producing
-- arrays.  This is perhaps a bit too conservative - we could track
-- exactly which are being consumed and keep a blacklist.
handleDuplicates (esubsts, nsubsts) pat e
  | any isArrayIdent $ S.toList $ patIdents pat =
    (pat, e, (esubsts, nsubsts))
handleDuplicates (esubsts, nsubsts) pat e =
  case M.lookup (substituteNames nsubsts e) esubsts of
    Just e' -> (pat, e', (esubsts, mkSubsts pat e' `M.union` nsubsts))
    Nothing -> (pat, e,
                case patToExp pat of
                  Nothing   -> (esubsts, nsubsts)
                  Just pate -> (M.insert e pate esubsts, nsubsts))

-- End of CSE stuff.  It's used in 'addBindings'.

addBindings :: Need -> Exp -> Exp
addBindings need =
  foldl (.) id $ snd $ mapAccumL comb (M.empty, newDupeState) $
  inDepOrder $ S.toList $ needBindings need
  where comb (m,ds) bind@(LoopBind mergepat mergeexp loopvar
                              boundexp loopbody) =
          ((m `M.union` distances m bind,ds),
           \inner -> DoLoop mergepat mergeexp loopvar boundexp
                     loopbody inner $ srclocOf inner)
        comb (m,ds) (LetBind pat e alts) =
          let add pat' e' =
                let (pat'',e'',ds') = handleDuplicates ds pat' e'
                in ((m `M.union` distances m (LetBind pat' e' []),ds'),
                    \inner -> LetPat pat'' e'' inner $ srclocOf inner)
          in case map snd $ sortBy (comparing fst) $ map (score m) $ (pat,e):alts of
               (pat',e'):_ -> add pat' e'
               _           -> add pat e
        comb (m,ds) bind@(LetWithBind cs dest src is ve) =
          ((m `M.union` distances m bind,ds),
           \inner -> LetWith cs dest src is ve inner $ srclocOf inner)

score :: M.Map VName Int -> (TupIdent, Exp) -> (Int, (TupIdent, Exp))
score m (p, Var k) =
  (fromMaybe (-1) $ M.lookup (identName k) m, (p,Var k))
score m (p, e) =
  (S.fold f 0 $ freeNamesInExp e, (p, e))
  where f k x = case M.lookup k m of
                  Just y  -> max x y
                  Nothing -> x

expCost :: Exp -> Int
expCost (Map {}) = 1
expCost (Map2 {}) = 1
expCost (Filter {}) = 1
expCost (Filter2 {}) = 1
expCost (Reduce {}) = 1
expCost (Reduce2 {}) = 1
expCost (Scan {}) = 1
expCost (Scan2 {}) = 1
expCost (Redomap {}) = 1
expCost (Redomap2 {}) = 1
expCost (Transpose {}) = 1
expCost (Copy {}) = 1
expCost (Concat {}) = 1
expCost (Split {}) = 1
expCost (Reshape {}) = 1
expCost (DoLoop {}) = 1
expCost (Replicate {}) = 1
expCost _ = 0

distances :: M.Map VName Int -> BindNeed -> M.Map VName Int
distances m need = M.fromList [ (k, d+cost) | k <- S.toList outs ]
  where d = S.fold f 0 ins
        (outs, ins, cost) =
          case need of
            LetBind pat e _ ->
              (patNames pat, freeNamesInExp e, expCost e)
            LetWithBind _ dest src is ve ->
              (S.singleton $ identName dest,
               identName src `S.insert`
               mconcat (map freeNamesInExp (ve:is)),
               1)
            LoopBind pat mergeexp _ bound loopbody ->
              (patNames pat,
               mconcat $ map freeNamesInExp [mergeexp, bound, loopbody],
               1)
        f k x = case M.lookup k m of
                  Just y  -> max x y
                  Nothing -> x

inDepOrder :: [BindNeed] -> [BindNeed]
inDepOrder = flattenSCCs . stronglyConnComp . buildGraph
  where buildGraph bnds =
          [ (bnd, provides bnd, deps) |
            bnd <- bnds,
            let deps = [ provides dep | dep <- bnds, dep `mustPrecede` bnd ] ]

mustPrecede :: BindNeed -> BindNeed -> Bool
bnd1 `mustPrecede` bnd2 =
  not $ S.null $ (provides bnd1 `S.intersection` requires bnd2) `S.union`
                 (consumedInExp e2 `S.intersection` requires bnd1)
  where e2 = asTail bnd2

anyIsFreeIn :: S.Set VName -> Exp -> Bool
anyIsFreeIn ks = (ks `intersects`) . S.map identName . freeInExp

intersects :: Ord a => S.Set a -> S.Set a -> Bool
intersects a b = not $ S.null $ a `S.intersection` b

type BlockPred = Exp -> BindNeed -> Bool

orIf :: BlockPred -> BlockPred -> BlockPred
orIf p1 p2 body need = p1 body need || p2 body need

splitHoistable :: BlockPred -> Exp -> Need -> (Need, Need)
splitHoistable block body (Need needs) =
  let (blocked, hoistable, _) =
        foldl split (S.empty, S.empty, S.empty) $
        inDepOrder $ S.toList needs
  in (Need blocked, Need hoistable)
  where split (blocked, hoistable, ks) need =
          case need of
            LetBind pat e es ->
              let bad e' = block body (LetBind pat e' []) || ks `anyIsFreeIn` e'
                  badAlt (_, e') = bad e'
              in case (bad e, filter (not . badAlt) es) of
                   (True, [])     ->
                     (need `S.insert` blocked, hoistable,
                      patNames pat `S.union` ks)
                   (True, (pat', e'):es') ->
                     (blocked, LetBind pat' e' es' `S.insert` hoistable, ks)
                   (False, es')   ->
                     (blocked, LetBind pat e es' `S.insert` hoistable, ks)
            _ | requires need `intersects` ks || block body need ->
                (need `S.insert` blocked, hoistable, provides need `S.union` ks)
              | otherwise ->
                (blocked, need `S.insert` hoistable, ks)

blockIfSeq :: [BlockPred] -> HoistM Exp -> HoistM Exp
blockIfSeq ps m = foldl (flip blockIf) m ps

blockIf :: BlockPred -> HoistM Exp -> HoistM Exp
blockIf block m = pass $ do
  (body, needs) <- listen m
  let (blocked, hoistable) = splitHoistable block body needs
  return (addBindings blocked body, const hoistable)

blockAllHoisting :: HoistM Exp -> HoistM Exp
blockAllHoisting = blockIf $ \_ _ -> True

hasFree :: S.Set VName -> BlockPred
hasFree ks _ need = ks `intersects` requires need

isNotSafe :: BlockPred
isNotSafe _ = not . safeExp . asTail

isNotCheap :: BlockPred
isNotCheap _ = not . cheap . asTail
  where cheap (Var _)      = True
        cheap (Literal {}) = True
        cheap (BinOp _ e1 e2 _ _) = cheap e1 && cheap e2
        cheap (TupLit es _) = all cheap es
        cheap (Not e _) = cheap e
        cheap (Negate e _ _) = cheap e
        cheap (LetPat _ e body _) = cheap e && cheap body
        cheap _ = False

uniqPat :: TupIdent -> Bool
uniqPat (Wildcard t _) = unique t
uniqPat (Id k)         = unique $ identType k
uniqPat (TupId pats _) = any uniqPat pats

isUniqueBinding :: BlockPred
isUniqueBinding _ (LoopBind pat _ _ _ _)     = uniqPat pat
isUniqueBinding _ (LetBind pat _ _)          = uniqPat pat
isUniqueBinding _ (LetWithBind _ dest _ _ _) = unique $ identType dest

isConsumed :: BlockPred
isConsumed body need =
  provides need `intersects` consumedInExp body

commonNeeds :: Need -> Need -> (Need, Need, Need)
commonNeeds n1 n2 = (mempty, n1, n2) -- Placeholder.

hoistCommon :: HoistM Exp -> HoistM Exp -> HoistM (Exp, Exp)
hoistCommon m1 m2 = pass $ do
  (body1, needs1) <- listen m1
  (body2, needs2) <- listen m2
  let splitOK = splitHoistable $ isNotSafe `orIf` isNotCheap
      (needs1', safe1) = splitOK body1 needs1
      (needs2', safe2) = splitOK body2 needs2
      (common, needs1'', needs2'') = commonNeeds needs1' needs2'
  return ((addBindings needs1'' body1,
           addBindings needs2'' body2),
          const $ mconcat [safe1, safe2, common])

hoistInExp :: Exp -> HoistM Exp
hoistInExp (If c e1 e2 t loc) = do
  c' <- hoistInExp c
  (e1',e2') <- hoistCommon (hoistInExp e1) (hoistInExp e2)
  return $ If c' e1' e2' t loc
hoistInExp (LetPat pat e body _) = do
  e' <- hoistInExp e
  bindLet pat e' $ hoistInExp body
hoistInExp (LetWith cs dest src idxs ve body _) = do
  idxs' <- mapM hoistInExp idxs
  ve' <- hoistInExp ve
  bindLetWith cs dest src idxs' ve' $ hoistInExp body
hoistInExp (DoLoop mergepat mergeexp loopvar boundexp loopbody letbody _) = do
  mergeexp' <- hoistInExp mergeexp
  boundexp' <- hoistInExp boundexp
  loopbody' <- blockIfSeq [hasFree boundnames, isConsumed] $
               hoistInExp loopbody
  bindLoop mergepat mergeexp' loopvar boundexp' loopbody' $ hoistInExp letbody
  where boundnames = identName loopvar `S.insert` patNames mergepat
hoistInExp e@(Map2 cs (TupleLambda params _ _ _) arrexps _ _) =
  hoistInSOAC e arrexps $ \ks ->
    withShapes (zip (map (Id . fromParam) params) $ map (slice cs 1) ks) $
    withShapes (sameOuterShapesExps cs arrexps) $
    hoistInExpBase e
hoistInExp e@(Reduce2 cs (TupleLambda params _ _ _) accexps arrexps _ _) =
  hoistInSOAC e arrexps $ \ks ->
    withShapes (zip (map (Id . fromParam) $ drop (length accexps) params)
               $ map (slice cs 1) ks) $
    withShapes (sameOuterShapesExps cs arrexps) $
    hoistInExpBase e
hoistInExp e@(Scan2 cs (TupleLambda params _ _ _) accexps arrexps _ _) =
  hoistInSOAC e arrexps $ \arrks ->
  hoistInSOAC e accexps $ \accks ->
    let (accparams, arrparams) = splitAt (length accexps) $
                                 map fromParam params in

    withShapes (map (first Id) $ zip arrparams $
                map (slice cs 1) arrks) $
    withShapes (map (first Id) $ filter (isArrayIdent . fst) $
                zip accparams $ map (slice cs 0) accks) $
    withShapes (sameOuterShapesExps cs arrexps) $
    hoistInExpBase e
hoistInExp e@(Redomap2 cs (TupleLambda redparams _ _ _) (TupleLambda mapparams _ _ _)
              accexps arrexps _ _) =
  hoistInSOAC e arrexps $ \ks ->
    withShapes (zip (map (Id . fromParam) mapparams) $ map (slice cs 1) ks) $
    withShapes (zip (map (Id . fromParam) $ drop (length accexps) redparams)
               $ map (slice cs 1) ks) $
    withShapes (sameOuterShapesExps cs arrexps) $
    hoistInExpBase e
hoistInExp e = hoistInExpBase e

hoistInExpBase :: Exp -> HoistM Exp
hoistInExpBase = mapExpM hoist
  where hoist = identityMapper {
                  mapOnExp = hoistInExp
                , mapOnTupleLambda = hoistInTupleLambda
                }

hoistInTupleLambda :: TupleLambda -> HoistM TupleLambda
hoistInTupleLambda (TupleLambda params body rettype loc) = do
  body' <- blockIf (hasFree params' `orIf` isUniqueBinding) $ hoistInExp body
  return $ TupleLambda params body' rettype loc
  where params' = S.fromList $ map identName params

arrVars :: [Exp] -> Maybe [Ident]
arrVars = mapM arrVars'
  where arrVars' (Var k) = Just k
        arrVars' _       = Nothing

hoistInSOAC :: Exp -> [Exp] -> ([Ident] -> HoistM Exp) -> HoistM Exp
hoistInSOAC e arrexps m =
  case arrVars arrexps of
    Nothing -> hoistInExpBase e
    Just ks -> m ks
