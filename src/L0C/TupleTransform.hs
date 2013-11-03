-- |
--
-- This module implements a transformation on L0 programs that
-- simplifies various uses of tuples.  The input program must be
-- uniquely named (as by the "L0.Renamer" module).  The output program
-- has the following properties:
--
--    * No function accepts a tuple as an argument.  Instead, they
--    have been rewritten to accept the tuple components explicitly.
--
--    * All tuples are flat - that is, their components are not
--    tuples.  @(t1,(t2,t3))@ is rewritten to @(t1,t2,t3)@.
--
--    * There are no arrays of tuples.  @[(t1,t2)]@ is rewritten to
--    @([t1], [t2])@.
--
--    * All bindings are full.  @let v = (x,y)@ is rewritten to @let
--    (v_1, v_2) = (x,y)@.  Combined with the first property, this
--    implies that no variable is ever bound to a tuple.
--
--    * SOACs are converted to their tuple versions.
--
module L0C.TupleTransform
  ( transformProg
  , transformType )
  where

import Control.Applicative
import Control.Monad.State
import Control.Monad.Reader
import Control.Monad.Writer

import qualified Data.Array as A
import qualified Data.Map as M
import Data.Maybe
import Data.List
import Data.Loc

import L0C.L0
import L0C.FreshNames

-- | Perform the tuple transformation on an entire program.
transformProg :: Prog -> Prog
transformProg prog =
  Prog $ runTransformM $ mapM transformFun $ progFunctions prog
  where runTransformM m = evalState (runReaderT m newEnv) newState
        newState = TransformState $ newNameSourceForProg prog
        newEnv = TransformEnv M.empty

data TransformState = TransformState {
    envNameSrc :: VNameSource
  }

data Replacement = ArraySubst Ident [Ident]
                 | TupleSubst [Ident]

data TransformEnv = TransformEnv {
    envSubsts :: M.Map VName Replacement
  }

type TransformM = ReaderT TransformEnv (State TransformState)

new :: String -> TransformM VName
new k = do (name, src) <- gets $ flip newVName k . envNameSrc
           modify $ \s -> s { envNameSrc = src }
           return name

flattenTypes :: [TypeBase als VName] -> [TypeBase als VName]
flattenTypes = concatMap flatten
  where flatten (Elem (Tuple ts)) = flattenTypes ts
        flatten t                 = [t]

transformElemType :: Monoid (als VName) =>
                     ElemTypeBase als VName -> ElemTypeBase als VName
transformElemType (Tuple elemts) =
  Tuple $ flattenTypes $ map transformType elemts
transformElemType t = t

transformElemType' :: Monoid (als VName) =>
                     ElemTypeBase als VName -> ElemTypeBase als VName
transformElemType' (Tuple elemts) =
  Tuple $ flattenTypes $ map transformType' elemts
transformElemType' t = t

-- | Perform the tuple transformation on a single type.
--
-- Example (the 'setAliases' part is to disambiguate the type of the
-- aliasing information):
--
-- >>> transformType $ (Elem $ Tuple [Elem $ Tuple [Elem Int, Elem Real], Elem Char]) `setAliases` NoInfo
-- Elem (Tuple [Elem Int,Elem Int,Elem Real,Elem Real,Elem Char])
transformType :: Monoid (als VName) => TypeBase als VName -> TypeBase als VName
transformType t@(Array {}) =
  case transformType' t of Elem (Tuple ets) -> Elem $ Tuple $ Elem Bool : ets
                           t'               -> t'
transformType (Elem et) = Elem $ transformElemType et

transformType' :: Monoid (als VName) => TypeBase als VName -> TypeBase als VName
transformType' (Array (Tuple elemts) size u als) =
  Elem $ Tuple $ flattenTypes (map (transformType' . arr) elemts)
  where arr t = arrayOf t size u `setAliases` als
transformType' (Array elemt size u als) =
  case ets of
    [et] -> et
    _    -> Elem (Tuple ets) `setAliases` als
  where ets = case transformElemType' $ elemt `setElemAliases` als of
                Tuple elemts -> flattenTypes $ map (transformType' . arr) elemts
                elemt'       -> [arrayOf (Elem elemt') size u]
        arr t = arrayOf t size u
transformType' (Elem et) = Elem $ transformElemType' et

flattenValues :: [Value] -> [Value]
flattenValues = concatMap flatten
  where flatten (TupVal vs) = vs
        flatten v           = [v]

transformValue :: Value -> Value
transformValue (ArrayVal arr rt) =
  case transformType $ addNames rt of
    Elem (Tuple ts)
      | [] <- A.elems arr ->
        TupVal $ LogVal True : flattenValues (map emptyOf ts)
      | otherwise         ->
        TupVal $ LogVal True : flattenValues (zipWith asarray (flattenTypes ts) $ transpose arrayvalues)
    rt' -> ArrayVal arr $ removeNames rt'
  where emptyOf t = blankValue $ arrayType 1 t Nonunique
        asarray t vs = transformValue $ arrayVal vs t
        arrayvalues = map (tupleValues . transformValue) $ A.elems arr
        tupleValues (TupVal vs) = vs
        tupleValues v = [v]
        -- Above should never happen in well-typed program.
transformValue (TupVal vs) = TupVal $ flattenValues $ map transformValue vs
transformValue v = v

transformIdent :: Ident -> Ident
transformIdent (Ident name t loc) = Ident name (transformType t) loc

transformFun :: FunDec -> TransformM FunDec
transformFun (fname,rettype,params,body,loc) =
  binding (map fromParam params) $ \params' -> do
    body' <- transformExp body
    return (fname, rettype', map toParam params', body', loc)
  where rettype' = transformType rettype

data TransformRes = FlatTuple [Ident]
                  | TupleArray Ident [Ident]
                  | Simple Ident

transformParam :: Ident -> TransformM TransformRes
transformParam param =
  case (identType param', identType param) of
    (Elem (Tuple (ct:ts)), Array {}) -> do
      ns <- mapM (liftM fst . newVar loc base) ts
      cert <- fst <$> newVar loc ("zip_cert_" ++ base) ct
      return $ TupleArray cert ns
    (Elem (Tuple ts), _) ->
      -- We know from transformIdent that none of the element
      -- types are themselves tuples.
      FlatTuple <$> mapM (liftM fst . newVar loc base) ts
    _ -> return $ Simple param'
  where param' = transformIdent param
        loc = srclocOf param
        base = nameToString $ baseName $ identName param

binding :: [Ident] -> ([Ident] -> TransformM a) -> TransformM a
binding params m = do
  (params', substs) <- runWriterT $ liftM concat . forM params $ \param -> do
    param' <- lift $ transformParam param
    case param' of
      Simple k -> return [k]
      FlatTuple ks -> do
        tell $ M.singleton (identName param) $ TupleSubst ks
        return ks
      TupleArray c ks -> do
        tell $ M.singleton (identName param) $ ArraySubst c ks
        return $ c:ks
  let bind env = env { envSubsts = substs `M.union` envSubsts env }
  local bind $ m params'

bindingPat :: TupIdent -> (TupIdent -> TransformM a) -> TransformM a
bindingPat (Wildcard t loc) m =
  case transformType t of
    Elem (Tuple ets) -> m $ TupId (map (`Wildcard` loc) ets) loc
    t' -> m $ Wildcard t' loc
bindingPat (Id k) m = do
  p <- transformParam k
  case p of
    Simple k'       -> m $ Id k'
    FlatTuple ks    -> substing ks $ TupleSubst ks
    TupleArray c ks -> substing (c:ks) $ ArraySubst c ks
  where substing ks sub =
          let bind env =
                env { envSubsts = M.insert (identName k) sub $ envSubsts env }
          in local bind $ m $ TupId (map Id ks) $ srclocOf k
bindingPat (TupId pats loc) m = do
  (ks, substs) <- runWriterT $ concat <$> mapM delve pats
  let bind env = env { envSubsts = substs `M.union` envSubsts env }
  local bind $ m $ TupId ks loc
    where delve (Id k) = do
            p <- lift $ transformParam k
            case p of
              Simple k'    -> return [Id k']
              FlatTuple ks -> do
                tell $ M.singleton (identName k) $ TupleSubst ks
                return $ map Id ks
              TupleArray c ks -> do
                tell $ M.singleton (identName k) $ ArraySubst c ks
                return $ map Id $ c : ks
          delve (Wildcard t _) =
            case transformType t of
              Elem (Tuple ets) -> return $ map (`Wildcard` loc) ets
              t' -> return [Wildcard t' loc]
          delve (TupId pats' _) =
            concat <$> mapM delve pats'


flattenExps :: [Exp] -> [Exp]
flattenExps = concatMap flatten
  where flatten (TupLit es _) = es
        flatten e             = [e]

transformExp :: Exp -> TransformM Exp

transformExp (Var var) = do
  subst <- asks $ M.lookup (identName var) . envSubsts
  case subst of
    Nothing -> return $ Var var
    Just (ArraySubst c ks) -> return $ TupLit (map Var $ c:ks) $ srclocOf var
    Just (TupleSubst ks)   -> return $ TupLit (map Var ks) $ srclocOf var

transformExp (Index cs vname idxs outtype loc) = do
  idxs' <- mapM transformExp idxs
  subst <- asks $ M.lookup (identName vname) . envSubsts
  case subst of
    Just (ArraySubst _ [v])
      | rt <- stripArray (length idxs') $ identType v,
        arrayDims rt == 0 ->
      return $ Index cs v idxs' rt loc
    Just (ArraySubst c vs) -> do
      let index v = Index [c] v idxs'
                    (stripArray (length idxs') $ identType v) loc
      mergeCerts (c:cs) $ \c' ->
        return $ case map index vs of
                   []   -> TupLit [] loc
                   a:as | arrayDims (typeOf a) == 0 -> TupLit (a:as) loc
                        | otherwise -> tuplit c' loc $ a:as
    _ -> return $ Index cs vname idxs' outtype loc

transformExp (TupLit es loc) = do
  (wrap, es') <-
    foldM comb (id, []) =<< flattenExps <$> mapM transformExp es
  return $ wrap $ TupLit (reverse es') loc
  where
    comb (wrap, es') e =
      case typeOf e of
        Elem (Tuple ts) -> do
          (names, namevs) <- unzip <$> mapM (newVar loc "tuplit_elem") ts
          return (\body -> wrap $ LetPat (TupId (map Id names) loc) e body loc,
                  reverse namevs ++ es')
        _ -> return (wrap, e:es')

transformExp (ArrayLit [] et loc) =
  return $ case transformType et of
             Elem (Tuple ets) ->
               TupLit (given loc : [ ArrayLit [] et' loc | et' <- ets ]) loc
             et' -> ArrayLit [] et' loc

transformExp (ArrayLit es rowtype loc) =
  tupsToIdentList es $ \aes -> do
  let (cs, es') = unzip aes
  case transformType rowtype of
    Elem (Tuple ets) -> do
      let arraylit ks et = ArrayLit (map Var ks) et loc
      mergeCerts (catMaybes cs) $ \c ->
        return $ tuplit c loc (zipWith arraylit (transpose es') ets)
    et' -> return $ ArrayLit (map (tuplit Nothing loc . map Var) es') et' loc

transformExp (Apply fname args rettype loc) =
  tupsToIdentList (map fst args) $ \args' ->
    let args'' = concatMap flatten $ zip args' $ map snd args
    in return $ Apply fname args'' rettype' loc
  where rettype' = transformType rettype
        flatten ((c, ks), d) =
          [ (Var k, d) | k <- maybeToList c ++ ks ]


transformExp (LetPat pat e body loc) = do
  e' <- transformExp e
  bindingPat pat $ \pat' -> do
    body' <- transformExp body
    return $ LetPat pat' e' body' loc

transformExp (DoLoop mergepat mergeexp i bound loopbody letbody loc) = do
  bound' <- transformExp bound
  mergeexp' <- transformExp mergeexp
  bindingPat mergepat $ \mergepat' -> do
    loopbody' <- transformExp loopbody
    letbody' <- transformExp letbody
    return $ DoLoop mergepat' mergeexp' i bound' loopbody' letbody' loc

transformExp (LetWith cs name src idxs ve body loc) = do
  idxs' <- mapM transformExp idxs
  tupToIdentList (Var src) $ \c1 srcs ->
    tupToIdentList ve $ \c2 vnames -> do
      dsts <- map fst <$> mapM (newVar loc "letwith_dst" . identType) srcs
      mergeCerts (catMaybes [c1,c2]++cs) $ \c -> do
        let comb olde (dname, sname, vname) inner =
              LetWith cs dname sname idxs' (Var vname) (olde inner) loc
            lws = foldl comb id $ zip3 dsts srcs vnames
        inner <- transformExp $ LetPat (Id name)
                 (tuplit c loc (map Var dsts)) body loc
        return $ lws inner

transformExp (Replicate ne ve loc) = do
  ne' <- transformExp ne
  ve' <- transformExp ve
  case typeOf ve' of
    Elem (Tuple _) ->
      tupToIdentList ve $ \_ ves -> do
      (n, nv) <- newVar loc "n" $ Elem Int
      let repexp v = Replicate nv (Var v) loc
          nlet body = LetPat (Id n) ne' body loc
      return $ nlet $ TupLit (given loc : map repexp ves) loc
    _ -> return $ Replicate ne' ve' loc

transformExp (Size cs i e loc) = do
  e' <- transformExp e
  tupToIdentList e $ \c ks ->
    case ks of
      (k:_) -> return $ Size (certify c cs) i (Var k) loc
      []    -> return $ Size (certify c cs) i e' loc -- Will this ever happen?

transformExp (Unzip e _ _) =
  tupToIdentList e $ \_ ks ->
    return $ TupLit (map Var ks) $ srclocOf e

transformExp (Zip es loc) =
  tupsToIdentList (map fst es) $ \lst ->
  let (cs1, names) = splitCertExps lst
  in case names of
       [] -> return $ TupLit [] loc
       _ -> do
         let namevs = map Var names
             rows e = Size [] 0 e loc
             ass e1 e2 = Assert (BinOp Equal (rows e1) (rows e2) (Elem Bool) loc) loc
             assertions = zipWith ass namevs $ drop 1 namevs
         (cs2, bindcs) <- bindVarsM "zip_assert" assertions
         bindcs <$> mergeCerts (cs1++cs2) (\c -> return $ tuplit c loc namevs)

transformExp (Iota e loc) = do
  e' <- transformExp e
  return $ Iota e' loc

transformExp (Transpose cs k n e loc) =
  tupToIdentList e $ \c vs ->
  mergeCerts (certify c cs) $ \cs' ->
  return $ tuplit cs' loc
           [Transpose (certify cs' []) k n (Var v) loc | v <- vs]

transformExp (Reshape cs shape e loc) =
  tupToIdentList e $ \c ks ->
  mergeCerts (certify c cs) $ \cs' ->
  return $ tuplit cs' loc
           [Reshape (certify cs' []) shape (Var k) loc | k <- ks]

transformExp (Split cs nexp arrexp eltype loc) = do
  nexp' <- transformExp nexp
  arrexp' <- transformExp arrexp
  case typeOf arrexp' of
    Elem (Tuple (_:ets)) ->
      tupToIdentList arrexp $ \c arrs ->
      mergeCerts (certify c cs) $ \cs' -> do
      (n, letn) <- bindVarM "split_n" nexp'
      partnames <- forM ets $ \et -> do
                     a <- fst <$> newVar loc "split_a" et
                     b <- fst <$> newVar loc "split_b" et
                     return (a, b)
      let cert = maybe (given loc) Var cs'
          combsplit olde (arr, (a,b), et) inner =
            olde $ LetPat (TupId [Id a, Id b] loc)
                   (Split (certify c []) (Var n) (Var arr) et loc) inner loc
          letsplits = foldl combsplit id $
                      zip3 arrs partnames $
                      map (stripArray 1) ets
          els = (cert : map (Var . fst) partnames) ++
                (cert : map (Var . snd) partnames)
      return $ letn $ letsplits $ TupLit els loc
    _ -> return $ Split cs nexp' arrexp' (transformType eltype) loc

transformExp (Concat cs x y loc) = do
  x' <- transformExp x
  y' <- transformExp y
  case typeOf x' of -- Both x and y have same type.
    Elem (Tuple _) ->
      tupToIdentList x $ \xc xs ->
      tupToIdentList y $ \yc ys -> do
      let certs = catMaybes [xc,yc]++cs
          conc xarr yarr = transformExp $
            Concat certs (Var xarr) (Var yarr) loc
      concs <- zipWithM conc xs ys
      mergeCerts certs $ \c' ->
        return $ tuplit c' loc concs
    _ -> return $ Concat cs x' y' loc

transformExp e@(Map lam arr tp pmap) =
  transformLambda lam $ \lam' ->
  tupToIdentList arr $ \c arrs ->
  let cs = certify c []
  in untupleSOAC cs (typeOf e) $
       Map2 cs (tuplifyLam lam') (map Var arrs)
               (untupleType $ transformType' tp) pmap

transformExp (Reduce lam ne arr tp pos) =
  transformLambda lam $ \lam' ->
  tupToIdentList arr $ \c1 arrs ->
  tupToIdentList ne $ \c2 nes ->
  untupleDeclExp (lambdaReturnType lam) $
  Reduce2 (catMaybes [c1,c2]) (tuplifyLam lam') (map Var nes) (map Var arrs)
          (untupleType $ transformType' tp) pos

transformExp e@(Scan lam ne arr tp pscan) =
  transformLambda lam $ \lam' ->
  tupToIdentList arr $ \c1 arrs ->
  tupToIdentList ne $ \c2 nes ->
  let cs = catMaybes [c1,c2]
  in untupleSOAC cs (typeOf e) $
       Scan2 cs (tuplifyLam lam') (map Var nes) (map Var arrs)
                (untupleType $ transformType' tp) pscan

transformExp e@(Filter lam arr _ loc) =
  transformLambda lam $ \lam' ->
  tupToIdentList arr $ \c arrs ->
  let cs = catMaybes [c]
  in untupleSOAC cs (typeOf e) $
       Filter2 cs (tuplifyLam lam') (map Var arrs) loc

transformExp (Redomap lam1 lam2 ne arr tp1 loc) =
  transformLambda lam1 $ \lam1' ->
  transformLambda lam2 $ \lam2' ->
  tupToIdentList arr $ \c1 arrs ->
  tupToIdentList ne $ \c2 nes ->
  untupleDeclExp (lambdaReturnType lam1) $
    Redomap2 (catMaybes [c1,c2]) (tuplifyLam lam1') (tuplifyLam lam2')
             (map Var nes) (map Var arrs) (untupleType $ transformType' tp1) loc

transformExp (Map2 cs1 lam arrs tps loc) =
  transformTupleLambda lam $ \lam' ->
  tupsToIdentList arrs $ \arrlst ->
  let (cs2, arrs') = splitCertExps arrlst
  in return $ Map2 (cs1++cs2) lam'
                (map Var arrs')
                (flattenTypes $ map transformType tps) loc

transformExp (Reduce2 cs1 lam nes arrs tps loc) =
  transformTupleLambda lam $ \lam' ->
  tupsToIdentList arrs $ \arrlst ->
  tupsToIdentList nes $ \nelst ->
    let (cs2, arrs') = splitCertExps arrlst
        (cs3, nes') = splitCertExps nelst
    in return $ Reduce2 (cs1++cs2++cs3) lam' (map Var nes') (map Var arrs')
                        (flattenTypes $ map transformType tps) loc

transformExp (Scan2 cs1 lam nes arrs tps loc) =
  transformTupleLambda lam $ \lam' ->
  tupsToIdentList arrs $ \arrlst ->
  tupsToIdentList nes $ \nelst ->
    let (cs2, arrs') = splitCertExps arrlst
        (cs3, nes') = splitCertExps nelst
    in return $ Scan2 (cs1++cs2++cs3) lam' (map Var nes') (map Var arrs')
                      (flattenTypes $ map transformType tps) loc

transformExp (Filter2 cs1 lam arrs loc) =
  transformTupleLambda lam $ \lam' ->
  tupsToIdentList arrs $ \arrlst ->
    let (cs2, arrs') = splitCertExps arrlst
    in return $ Filter2 (cs1++cs2) lam' (map Var arrs') loc

transformExp (Redomap2 cs1 lam1 lam2 nes arrs tps loc) =
  transformTupleLambda lam1 $ \lam1' ->
  transformTupleLambda lam2 $ \lam2' ->
  tupsToIdentList arrs $ \arrlst ->
  tupsToIdentList nes $ \nelst ->
    let (cs2, arrs') = splitCertExps arrlst
        (cs3, nes') = splitCertExps nelst
    in return $ Redomap2 (cs1++cs2++cs3) lam1' lam2'
                (map Var nes') (map Var arrs') (map transformType tps) loc

transformExp e = mapExpM transform e
  where transform = Mapper {
                      mapOnExp = transformExp
                    , mapOnType = return . transformType
                    , mapOnLambda = return -- Not used.
                    , mapOnTupleLambda = return -- Not used.
                    , mapOnPattern = return -- Not used.
                    , mapOnIdent = return -- Not used.
                    , mapOnValue = return . transformValue
                    }

tupToIdentList :: Exp -> (Maybe Ident -> [Ident] -> TransformM Exp)
               -> TransformM Exp
tupToIdentList e m = do
  e' <- transformExp e
  case (typeOf e', typeOf e) of
    (Elem (Tuple []), _) -> m Nothing []
    (Elem (Tuple (t:ts)), Array {}) -> do
      cert <- fst <$> newVar loc "tup_arr_cert" t
      names <- mapM (liftM fst . newVar loc "tup_arr_elem") ts
      LetPat (TupId (map Id $ cert : names) loc) e' <$> m (Just cert) names <*> pure loc
    (Elem (Tuple ts), _) -> do
      names <- mapM (liftM fst . newVar loc "tup_elem") ts
      LetPat (TupId (map Id names) loc) e' <$> m Nothing names <*> pure loc
    (t, _) -> case e' of
                Var k -> m Nothing [k] -- Just to avoid too many spurious bindings.
                _ -> do name <- fst <$> newVar loc "val" t
                        LetPat (Id name) e' <$> m Nothing [name] <*> pure loc
  where loc = srclocOf e

tupsToIdentList :: [Exp] -> ([(Maybe Ident, [Ident])] -> TransformM Exp)
                -> TransformM Exp
tupsToIdentList = tupsToIdentList' []
  where tupsToIdentList' acc [] m = m acc
        tupsToIdentList' acc (e:es) m =
          tupToIdentList e $ \c e' ->
            tupsToIdentList' (acc++[(c,e')]) es m

splitCertExps :: [(Maybe Ident, [Ident])] -> ([Ident], [Ident])
splitCertExps l = (mapMaybe fst l,
                   concatMap snd l)

mergeCerts :: [Ident] -> (Maybe Ident -> TransformM Exp) -> TransformM Exp
mergeCerts [] f = f Nothing
mergeCerts [c] f = f $ Just c
mergeCerts (c:cs) f = do
  cert <- fst <$> newVar loc "comb_cert" (Elem Bool)
  LetPat (Id cert) (Assert (conjoin loc $ c:cs) loc) <$> f (Just cert) <*> pure loc
  where loc = srclocOf c

cleanLambdaParam :: [Ident] -> Type -> TransformM ([Ident], [Exp])
cleanLambdaParam [] _ = return ([], [])
cleanLambdaParam ks@(k:_) t =
  case (ks, t, transformType t) of
    (_:ks', Array {}, Elem (Tuple _)) -> do
      (names, namevs) <- unzip <$> mapM (newVar loc "arg" . identType) ks'
      return (names, given loc : namevs)
    (_, Elem (Tuple ets), Elem (Tuple _)) -> do
      let comb (ks', params, es) et =
            case transformType et of
              Elem (Tuple ets') -> do
                (newparams, newes) <-
                  cleanLambdaParam (take (length ets') ks') et
                return (drop (length ets') ks', params++newparams, es++newes)
              _ -> do
                (newparams, newes) <-
                  cleanLambdaParam (take 1 ks') et
                return (drop 1 ks', params++newparams, es++newes)
      (_, params, es) <- foldM comb (ks, [], []) ets
      return (params, es)
    (_, _, _) -> do
      (names, namevs) <- unzip <$> mapM (newVar loc "arg" . identType) ks
      return (names, namevs)
  where loc = srclocOf k

lambdaBinding :: [Ident] -> ([Ident] -> (Exp -> Exp) -> TransformM a) -> TransformM a
lambdaBinding params m = do
  (params', (patpairs, substs)) <- runWriterT $ liftM concat . forM params $ \param -> do
    param' <- lift $ transformParam param
    case param' of
      Simple k -> return [k]
      FlatTuple [] -> return []
      FlatTuple ks@(k:_) -> do
        let loc = srclocOf k
        (ks', es) <- lift $ cleanLambdaParam ks $ identType param
        tell ([(TupId (map Id ks) loc, TupLit es loc)],
              M.singleton (identName param) $ TupleSubst ks)
        return ks'
      TupleArray c ks -> do
        let loc = srclocOf c
        (ks', es) <- lift $ cleanLambdaParam (c:ks) $ identType param
        tell ([(TupId (map Id $ c:ks) loc, TupLit es loc)],
              M.singleton (identName param) $ ArraySubst c ks)
        return ks'
  let bind env = env { envSubsts = substs `M.union` envSubsts env }
      comb outer (pat,e) inner = outer $ LetPat pat e inner $ srclocOf pat
      letf = foldl comb id patpairs
  local bind $ m params' letf

transformLambda :: Lambda -> (Lambda -> TransformM Exp) -> TransformM Exp
transformLambda (AnonymFun params body rettype loc) m = do
  lam <- lambdaBinding (map fromParam params) $ \params' letf -> do
           body' <- transformExp body
           return $ AnonymFun (map toParam params') (letf body') rettype' loc
  m lam
  where rettype' = toDecl $ transformType rettype
transformLambda (CurryFun fname curryargs rettype loc) m =
  transform curryargs []
  where transform [] curryargs' =
          m $ CurryFun fname curryargs' (transformType rettype) loc
        transform (a:as) curryargs' =
          tupToIdentList a $ \c ks ->
            transform as (curryargs' ++ map Var (certify c ks))

transformTupleLambda :: TupleLambda -> (TupleLambda -> TransformM Exp) -> TransformM Exp
transformTupleLambda (TupleLambda params body rettype loc) m = do
  lam <- binding (map fromParam params) $ \params' -> do
           body' <- transformExp body
           return $ TupleLambda (map toParam params') body' rettype' loc
  m lam
  where rettype' = map (toDecl . transformType) rettype

tuplifyLam :: Lambda -> TupleLambda
tuplifyLam (CurryFun {}) = error "no curries yet"
tuplifyLam (AnonymFun params body rettype loc) =
  TupleLambda params body' rettypes loc
  where (rettypes, body') =
          case rettype of
            Elem (Tuple ets) -> (ets, body)
            _                -> ([rettype],
                                 mapTails tuplifyLam' tuplifyType body)
        tuplifyLam' e = TupLit [e] loc

tuplifyType :: TypeBase als vn -> TypeBase als vn
tuplifyType (Elem (Tuple ets)) = Elem $ Tuple ets
tuplifyType t                  = Elem $ Tuple [t]

newVar :: SrcLoc -> String -> Type -> TransformM (Ident, Exp)
newVar loc name tp = do
  x <- new name
  return (Ident x tp loc, Var $ Ident x tp loc)

untupleDeclExp :: DeclType -> Exp -> TransformM Exp
untupleDeclExp = untupleExp . fromDecl

untupleExp :: Type -> Exp -> TransformM Exp
untupleExp t e = do
  let loc = srclocOf e
  case typeOf e of
    Elem (Tuple [et])
      | et `subtypeOf` t -> do
        (v, vn) <- newVar loc "untuple" et
        return $ LetPat (TupId [Id v] loc) e vn loc
    _ -> return e

untupleSOAC :: Certificates -> Type -> Exp -> TransformM Exp
untupleSOAC cs t e = do
  let loc = srclocOf e
  case typeOf e of
    Elem (Tuple [et])
      | et `subtypeOf` t -> untupleExp t e
    Elem (Tuple ets) -> do
      (names, namevs) <- unzip <$> mapM (newVar loc "soac_v") ets
      return $ LetPat (TupId (map Id names) loc) e
                      (TupLit (conjoin loc cs:namevs) loc) loc
    _ -> return e

untupleType :: Type -> [Type]
untupleType (Elem (Tuple ts)) = ts
untupleType t = [t]

tuplit :: Maybe Ident -> SrcLoc -> [Exp] -> Exp
tuplit _ _ [e] = e
tuplit Nothing loc es = TupLit (given loc:es) loc
tuplit (Just c) loc es = TupLit (Var c:es) loc

-- Name suggested by Spectrum.
given :: SrcLoc -> Exp
given = Literal $ LogVal True

certify :: Maybe Ident -> Certificates -> Certificates
certify k cs = maybeToList k ++ cs

bindVarM :: String -> Exp -> TransformM (Ident, Exp -> Exp)
bindVarM _ (Var k) =
  return (k, id)
bindVarM desc e = do
  k <- fst <$> newVar (srclocOf e) desc (typeOf e)
  return (k, \inner -> LetPat (Id k) e inner $ srclocOf e)

bindVarsM :: String -> [Exp] -> TransformM ([Ident], Exp -> Exp)
bindVarsM _ [] = return ([], id)
bindVarsM desc (e:es) = do
  (k, f) <- bindVarM desc e
  (ks, g) <- bindVarsM desc es
  return (k:ks, f . g)

conjoin :: SrcLoc -> [Ident] -> Exp
conjoin loc [] = given loc
conjoin loc (k:ks) =
  let conjoin' e1 e2 = And e1 e2 loc
  in foldl conjoin' (Var k) $ map Var ks
