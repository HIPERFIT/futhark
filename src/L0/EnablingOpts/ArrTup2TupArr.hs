{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables #-}

module L0.EnablingOpts.ArrTup2TupArr ( arr2tupProg )
  where
 
import Control.Monad.State
import Control.Applicative
import Control.Monad.Reader
--import Control.Monad.Writer

 
import Data.Generics hiding (typeOf)

--import qualified Data.Set as S
import qualified Data.Map as M

import L0.AbSyn
import Data.Array as A
import Data.Loc
 
import L0.FreshNames

--import L0.Traversals
import L0.EnablingOpts.EnablingOptErrors

import Debug.Trace

-----------------------------------------------------------------
-----------------------------------------------------------------
---- This file implements Array-of-Tuples to Tuple-of-Array  ----
----    transformation. In addition it also flatten tuples.  ----
---- I.e., after transformation, the program contains only   ----
----    flat tuples and types such as [(..,..)] are illegal! ----
---- Assumtions: the program is let normalized,              ---- 
----    e.g.,SOAC, function calls have their own let bindings----
---- Example: assume original program is
----    let arr = {(1, 'a')}    in
----    let res = (c, (arr, d)) in
----    let x   = f(res) in x
---- After transformation it becomes:
----    let (arr1, arr2) = ({1}, {'a'})                   in
----    let (res1, res2, res3, res4) = (c, arr1, arr2, d) in
----    let x = f((res1, res2, res3, res4)) in x
---- Then after copy prop it becomes:
----    let (arr1, arr2) = ({1}, {'a'}) in
----    let x = f(c, arr1, arr2, d) in x
-----------------------------------------------------------------
-----------------------------------------------------------------

data Arr2TupEnv = Arr2TupEnv {   
                    -- associates a var name in the orig prg to
                    -- the flat tuple it becomes after transf.
                    -- with the above example `res' is associated
                    -- with `[res1, res2, res3, res4]' vars
                    tupVtable  :: M.Map String [Ident Type] --(TupIdent Type)
                  }


newtype Arr2TupM a = Arr2TupM (StateT NameSource (ReaderT Arr2TupEnv (Either EnablingOptError)) a)
    deriving (  MonadState NameSource, 
                MonadReader (Arr2TupEnv),
                Monad, Applicative, Functor )


-- | Bind a name as a common (non-merge) variable.
bindVar :: Arr2TupEnv -> (String, [Ident Type]) -> Arr2TupEnv
bindVar env (name,val) =
  env { tupVtable = M.insert name val $ tupVtable env }

bindVars :: Arr2TupEnv -> [(String, [Ident Type])] -> Arr2TupEnv
bindVars = foldl bindVar

binding :: [(String, [Ident Type])] -> Arr2TupM a -> Arr2TupM a
binding bnds = local (`bindVars` bnds)


-- | The program normalizer runs in this monad.  The mutable
-- state refers to the fresh-names engine. The reader hides
-- the vtable that associates variable names with/to-be-substituted-for tuples pattern.
-- The 'Either' monad is used for error handling.
runNormM :: Prog Type -> Arr2TupM a -> Arr2TupEnv -> Either EnablingOptError a
runNormM prog (Arr2TupM a) =
    runReaderT (evalStateT a (newNameSourceForProg prog))

badArr2TupM :: EnablingOptError -> Arr2TupM a
badArr2TupM = Arr2TupM . lift . lift . Left

-- | Return a fresh, unique name.  The @String@ is prepended to the
-- name.
new :: String -> Arr2TupM String
new = state . newName


-----------------------------------------------------------------
--- Tuple Normalizer Entry Point: normalizes tuples@pgm level ---
-----------------------------------------------------------------

arr2tupProg :: Prog Type -> Either EnablingOptError (Prog Type)
arr2tupProg prog = do
    let env = Arr2TupEnv { tupVtable = M.empty }
    runNormM prog (mapM arr2tupFun prog) env



-----------------------------------------------------------------
-----------------------------------------------------------------
---- Normalizing a function: for every tuple param, e.g.,    ----
-----------------------------------------------------------------
-----------------------------------------------------------------

arr2tupFun :: FunDec Type -> Arr2TupM (FunDec Type)
arr2tupFun (fname, rettype, args, body, pos) = do
    --body' <- trace ("in function: "++fname++"\n") (arr2tupAbstrFun args body pos)
    let rettype' = toTupArrType rettype
    let args'    = map toTupArrIdent args
    body' <- arr2tupAbstrFun args' body pos
    return (fname, rettype', args', body', pos)


--------------------------------
---- Normalizing a Value    ----
--------------------------------

arr2tupVal :: SrcLoc -> Value -> Arr2TupM Value

arr2tupVal loc (TupVal tups) = do
    tups' <- mapM (arr2tupVal loc) tups
    let tupes = map (`Literal` loc) tups'
    tup_res <- foldM flattenTups (Literal (TupVal []) loc) tupes
    case tup_res of
        Literal v@(TupVal {}) _ -> return v
        _ ->  badArr2TupM $ EnablingOptError loc ("In arr2tupVal of TupVal: flattening a TupVal"
                                                  ++" does not result in a TupVal!!! ")

arr2tupVal loc (ArrayVal els tp) = do
    let tp' = toTupArrType tp
    els'   <- mapM (arr2tupVal loc) (A.elems els)
    case (tp', head els') of
        (Tuple tps' _ _, TupVal tupels) -> do 
            lstlst <- foldM concatTups (map (:[]) tupels) (tail els')
            let tuparrs = map (\(x,y)->ArrayVal (A.listArray (0,length els'-1) x) y) (zip lstlst tps')
            return $ TupVal tuparrs
        (Tuple {}, _) ->
            badArr2TupM $ EnablingOptError loc ("In arr2tupVal of ArrayVal: "
                                                ++" element of Tuple Type NOT a Tuple Value!!! ")
        _ -> return $ ArrayVal (A.listArray (0,length els'-1) els') tp'
    where
        concatTups :: [[Value]] -> Value -> Arr2TupM [[Value]]
        concatTups acc e = case e of
            TupVal tups ->
                if length acc /= length tups
                then badArr2TupM $ EnablingOptError loc ("In concatTups/arr2tupVal of ArrayVal: "
                                                         ++" two tuple elems of different length! ")
                else do let res = zipWith (\ x y -> x ++ [y]) acc tups
                        return res
            _ -> badArr2TupM $ EnablingOptError loc ("In concatTups/arr2tupVal of ArrayVal: "
                                                     ++" element NOT of Tuple Type! ")

arr2tupVal _ v = return v

-----------------------------------------------------------------
-----------------------------------------------------------------
---- Normalizing an expression                               ----
-----------------------------------------------------------------
-----------------------------------------------------------------

arr2tupExp :: Exp Type -> Arr2TupM (Exp Type)


-----------------------------------------
-----------------------------------------
---- Array/Tuple/Value Literals      ----
-----------------------------------------
-----------------------------------------

arr2tupExp (Literal v loc) = do 
    v' <- arr2tupVal loc v
    return $ Literal v' loc

arr2tupExp (TupLit tups pos) = do
    tups'   <- mapM arr2tupExp tups
    foldM flattenTups (Literal (TupVal []) pos) tups'

arr2tupExp (ArrayLit els tp pos) = do
    let tp' = toTupArrType tp
    els'   <- mapM arr2tupExp els
    case tp' of
        Tuple tps' _ _ -> do
            lstlst <- foldM concatTups (replicate (length tps') []) els'
            let tuparrs  = map (\(x,y)->ArrayLit x y pos) (zip lstlst tps')
            return $ TupLit tuparrs pos
        _ -> return $ ArrayLit els' tp' pos
{-
    case (tp', head els') of
        (Tuple tps' _ _, TupLit tupels _) -> do 
            lstlst <- foldM concatTups (map (\x -> [x]) tupels) (tail els')
            let tuparrs = map (\(x,y)->ArrayLit x y pos) (zip lstlst tps')
            return $ TupLit tuparrs pos
        (Tuple {}, _) ->
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of ArrayLit: "++ppExp 0 (head els')
                                                ++" element of Tuple Type NOT a Tuple Literal!!! ")
        _ -> return $ ArrayLit els' tp' pos
-}
    where
        concatTups :: [[Exp Type]] -> Exp Type -> Arr2TupM [[Exp Type]]
        concatTups acc e = case e of
            TupLit tups _ -> 
                if length acc /= length tups
                then badArr2TupM $ EnablingOptError pos ("In concatTups/arr2tupExp of ArrayLit: "
                                                         ++" two tuple elems of different length! ")
                else do let res = zipWith (\ x y -> x ++ [y]) acc tups
                        return res
            Literal (TupVal tups) _ ->
                if length acc /= length tups
                then badArr2TupM $ EnablingOptError pos ("In concatTups/arr2tupExp of ArrayLit: "
                                                         ++" two tuple elems of different length! ")
                else do let res = zipWith (\ x y -> x ++ [Literal y pos]) acc tups
                        return res                
            _ -> badArr2TupM $ EnablingOptError pos ("In concatTups/arr2tupExp of ArrayLit: "
                                                     ++" element NOT of Tuple Type! ")


-------------------------------------------------------
--- Var/Index: 
-------------------------------------------------------

arr2tupExp e@(Var (Ident vnm _ pos)) = do 
    -- vtable holds the result idents (of flattened type) 
    bnd <- asks $ M.lookup vnm . tupVtable
    case bnd of
        Nothing  -> return e
        Just ids -> do  let vars = map mkVarFromIdent ids 
                        if length vars == 1 
                        then return $ head vars
                        else return $ TupLit vars pos 
    where
        mkVarFromIdent idd = 
            Var Ident { identName = identName idd 
                      , identType = identType idd 
                      , identSrcLoc = pos
                      }
            
arr2tupExp (Index idd inds tp1 tp2 pos) = do
    inds' <- mapM arr2tupExp inds
    bnd   <- asks $ M.lookup (identName idd) . tupVtable
    case bnd of
        Nothing  -> return $ Index idd inds' tp1 tp2 pos
        Just ids -> do -- idd might have been an array of tuples:
                       -- note that the indexing code is duplicated; I expect
                       --     common subexpression elimination to clean it up!
                       -- should we also check that tp2' is consistent with the result?
                       indlst <- mapM (mkIndexFromIdent inds') ids
                       if length ids == 1
                       then return $ head indlst
                       else return $ TupLit indlst pos
    where
        mkIndexFromIdent :: [Exp Type] -> Ident Type -> Arr2TupM (Exp Type)
        mkIndexFromIdent newind iddd = 
            let (idnm, idtp) = ( identName iddd, identType iddd)
                iddd' = Ident { identName = idnm, identType   = idtp, identSrcLoc = pos }
                (idtp1, idtp2) = ( peelArray 1 idtp, peelArray (length newind) idtp ) 
            in case (idtp1, idtp2) of
                (Just t1, Just t2) -> return $ Index iddd' newind t1 t2 pos
                _ -> badArr2TupM $ EnablingOptError pos "In arr2tupExp of Index, array peeling failed) "

---------------------------------------
---------------------------------------
---- LET PATTERN                   ----
---------------------------------------
---------------------------------------

-----------------------------------------------
---- Map/Reduce/Scan/Filter/Mapall/redomap ----
-----------------------------------------------
arr2tupExp (Map lam arr tp1 tp2 pmap) = do
    let (tp1', tp2') = (toTupArrType tp1, toTupArrType tp2)
    lam' <- arr2tupLambda lam
    arr' <- arr2tupExp     arr
    arrs'<- tupArrToLstArr arr'
    return $ Map2 lam' arrs' tp1' tp2' pmap

arr2tupExp (Reduce lam ne arr tp pos) = do
    let tp' = toTupArrType tp
    lam' <- arr2tupLambda lam
    arr' <- arr2tupExp    arr
    arrs'<- tupArrToLstArr arr'
    ne'  <- arr2tupExp    ne
    return $ Reduce2 lam' ne' arrs' tp' pos

arr2tupExp (Scan lam ne arr tp pscan) = do
    let tp' = toTupArrType tp
    lam' <- arr2tupLambda lam
    arr' <- arr2tupExp    arr
    arrs'<- tupArrToLstArr arr'
    ne'  <- arr2tupExp    ne
    return $ Scan2 lam' ne' arrs' tp' pscan

arr2tupExp (Filter lam arr tp pfilt) = do
    let tp' = toTupArrType tp
    lam' <- arr2tupLambda lam
    arr' <- arr2tupExp    arr
    arrs'<- tupArrToLstArr arr'
    return $ Filter2 lam' arrs' tp' pfilt

arr2tupExp (Mapall lam arr tp1 tp2 pmap) = do
    let (tp1', tp2') = (toTupArrType tp1, toTupArrType tp2)
    lam' <- arr2tupLambda lam
    arr' <- arr2tupExp    arr
    arrs'<- tupArrToLstArr arr'
    return $ Mapall2 lam' arrs' tp1' tp2' pmap

arr2tupExp (Redomap lam1 lam2 ne arr tp1 tp2 pos) = do
    let (tp1', tp2') = (toTupArrType tp1, toTupArrType tp2)
    lam1' <- arr2tupLambda lam1
    lam2' <- arr2tupLambda lam2
    arr'  <- arr2tupExp    arr
    arrs'<- tupArrToLstArr arr'
    ne'   <- arr2tupExp    ne
    return $ Redomap2 lam1' lam2' ne' arrs' tp1' tp2' pos

----------------------------------------
---- BuiltIn Array functions:       ----
----   size, replicate, transpose,  ----
----   reshape, copy, split, concat.----
---- Assume that the argument is a  ----
----   tuple literal, i.e., this is ----
----   a property of let-norm       ----
----------------------------------------

arr2tupExp (Size arr pos) = do
    arr' <- arr2tupExp arr
    case (typeOf arr', arr') of
        -- just return the size of the first element
        (Tuple {}, TupLit (fsttup:_) _) -> return $ Size fsttup pos
        (Tuple {}, _) ->  
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Size, broken invariant: "
                                                ++" arg of tuple type NOT a tuple literal! ")
        _ -> return $ Size arr' pos

arr2tupExp (Replicate n arr pos) = do
    n'   <- arr2tupExp n
    arr' <- arr2tupExp arr
    case (typeOf arr', arr') of
        (Tuple {}, TupLit tups plit) -> do
            let reps = map (\x -> Replicate n' x pos) tups
            return $ TupLit reps plit
        (Tuple {}, _) -> 
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Replicate, broken invariant: "
                                                ++" arg of tuple type NOT a tuple literal! ")
        _ -> return $ Replicate n' arr' pos

arr2tupExp (Transpose arr pos) = do
    arr' <- arr2tupExp arr
    case (typeOf arr', arr') of
        (Tuple {}, TupLit tups plit) -> do
            let reps = map (`Transpose` pos) tups
            return $ TupLit reps plit
        (Tuple {}, _) -> 
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Transpose, broken invariant: "
                                                ++" arg of tuple type NOT a tuple literal! ")
        _ -> return $ Transpose arr' pos

arr2tupExp (Reshape newsz arr pos) = do
    newsz' <- mapM arr2tupExp newsz
    arr'   <- arr2tupExp arr
    case (typeOf arr', arr') of
        (Tuple {}, TupLit tups plit) -> do
            let reps = map (\x -> Reshape newsz' x pos) tups
            return $ TupLit reps plit
        (Tuple {}, _) -> 
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Reshape, broken invariant: "
                                                ++" arg of tuple type NOT a tuple literal! ")
        _ -> return $ Reshape newsz' arr' pos

arr2tupExp (Copy arr pos) = do
    arr' <- arr2tupExp arr
    case (typeOf arr', arr') of
        (Tuple {}, TupLit tups plit) -> do
            let reps = map (`Copy` pos) tups
            return $ TupLit reps plit
        (Tuple {}, _) -> 
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Copy, broken invariant: "
                                                ++" arg of tuple type NOT a tuple literal! ")
        _ -> return $ Copy arr' pos

arr2tupExp (Split n arr tp pos) = do
    let tp' = toTupArrType tp
    n'   <- arr2tupExp n
    arr' <- arr2tupExp arr
    case (typeOf arr', arr') of
        (Tuple {}, TupLit tups plit) -> do
            reps <- mapM (\x -> do eltp <- elemType $ typeOf x
                                   return $ Split n' x eltp pos) 
                         tups
            return $ TupLit reps plit
        (Tuple {}, _) -> 
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Split, broken invariant: "
                                                ++" arg of tuple type NOT a tuple literal! ")
        _ -> return $ Split n' arr' tp' pos

arr2tupExp (Concat arr1 arr2 tp pos) = do
    let tp' = toTupArrType tp
    arr1' <- arr2tupExp arr1
    arr2' <- arr2tupExp arr2
    case (typeOf arr1', arr1', arr2') of
        (Tuple {}, TupLit tups1 plit1, TupLit tups2 _) -> 
            if typeOf arr1' /= typeOf arr2'
            then badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Concat, broken invariant: "
                                                     ++" tuple types of arrays do not match! ")
            else do reps <- mapM (\(x,y) -> do eltp <- elemType $ typeOf x 
                                               return $ Concat x y eltp pos) 
                                 (zip tups1 tups2)
                    return $ TupLit reps plit1
        (Tuple {}, _, _) -> 
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Concat, broken invariant: "
                                                ++" arg of tuple type NOT a tuple literal! ")
        _ -> return $ Concat arr1' arr2' tp' pos

----------------------------------------------------------
---- zip/unzip are treated in connection with Let-Pat ----
----------------------------------------------------------

arr2tupExp (Zip _ pos) = 
    badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Zip, broken invariant: "
                                        ++" zip appears outside of a Let Pattern! ")

arr2tupExp (Unzip _ _ pos) = 
    badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Unzip, broken invariant: "
                                        ++" unzip appears outside of a Let Pattern! ")

--------------------------------------------------------
--- map2, reduce2, scan2, filter2, mapall2, redomap2 ---
---    SHOULD NOT EXIST IN THE INPUT PROGRAM!!!      ---
--------------------------------------------------------

arr2tupExp (Map2 _ _ _ _ pos) =  
    badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Map2, broken invariant: "
                                        ++" Map2 appears in the input program! ")
arr2tupExp (Reduce2 _ _ _ _ pos) =  
    badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Reduce2, broken invariant: "
                                        ++" Reduce2 appears in the input program! ")
arr2tupExp (Scan2 _ _ _ _ pos) =  
    badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Scan2, broken invariant: "
                                        ++" Scan2 appears in the input program! ")
arr2tupExp (Filter2 _ _ _ pos) =  
    badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Filter2, broken invariant: "
                                        ++" Filter2 appears in the input program! ")
arr2tupExp (Mapall2 _ _ _ _ pos) =  
    badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Mapall2, broken invariant: "
                                        ++" Mapall2 appears in the input program! ")
arr2tupExp (Redomap2 _ _ _ _ _ _ pos) =  
    badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Redomap2, broken invariant: "
                                        ++" Redomap2 appears in the input program! ")

-----------------------------
-----------------------------
---- LetPat/With/Do-Loop ----
-----------------------------
-----------------------------

----------------------------------------
---- BuiltIn Array functions: un/zip----
----   Unzip becomes a nop.         ----
----   Zip: replaced with assertZip.----
----------------------------------------

-- ToDo: modify copy propagation and dead-code elimination to 
--       do NOT remove the assertZip statement!!!
arr2tupExp (LetPat pat z@(Zip els pzip) body pos) = do
    let tp = toTupArrType $ typeOf z
    els' <- mapM (arr2tupExp . fst) els
    arrs <- case tp of
        Tuple{} -> return $ concatMap tupFlatten els'
        _       -> badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Let-Zip, broken invariant: "
                                                       ++" zip's (transformed) type not a tuple! ")
    let e' = TupLit arrs pzip 
    (pat', bnds) <- mkFullPattern pat
    body' <- binding bnds $ arr2tupExp body
    res <- distribPatExp pat' e' body' 

    -- `assertZip' results in a Boolean value
    -- (pat_assert, _) <- mkFullPattern pat
    tmp_nm <- new "assrt" 
    let pat_id = Ident { identName = tmp_nm
                       , identType = Bool pzip
                       , identSrcLoc = pzip  
                       }
    let e_assert = Apply "assertZip" arrs (Bool pzip) pzip -- tp pzip

    return $ LetPat (Id pat_id) e_assert res pos
    where 
        tupFlatten :: Exp Type -> [Exp Type]
        tupFlatten e = case e of
            TupLit tups _ -> tups
            _             -> [e]

-- ToDo: should we register somewhere the invariant 
--       that all unziped arrays have the same size ? 
arr2tupExp (LetPat pat (Unzip arr _ _) body pos) = do
    tup_arrs <- arr2tupExp arr
    _ <- case tup_arrs of
           TupLit ts _ -> return ts
           _ -> badArr2TupM $ EnablingOptError pos ("In arr2tupExp of Let-Unzip, broken invariant: "
                                                    ++" unziped array is not a TupLit! ")
    (pat', bnds) <- mkFullPattern pat
    body' <- binding bnds $ arr2tupExp body
    distribPatExp pat' tup_arrs body'

arr2tupExp (LetPat pat e body _) = do
    e'    <- arr2tupExp  e
    (pat', bnds) <- mkFullPattern pat
    body' <- binding bnds $ arr2tupExp body 
    distribPatExp pat' e' body'

arr2tupExp (DoLoop mergepat mergeexp idd n loopbdy letbdy pos) = do
    (mergepat', bnds) <- mkFullPattern mergepat
    mergeexp' <- arr2tupExp mergeexp
    n'    <- arr2tupExp n

    loopbdy' <- binding bnds $ arr2tupExp loopbdy
    letbdy'  <- binding bnds $ arr2tupExp letbdy

    return $ DoLoop mergepat' mergeexp' idd n' loopbdy' letbdy' pos
       
arr2tupExp (LetWith dst src inds el body pos) = do
    inds' <- mapM arr2tupExp inds

    bnd   <- asks $ M.lookup (identName src) . tupVtable
    let tpelm = toTupArrType $ typeOf el 
    case (tpelm, bnd) of
        (Tuple elm_tps _ _, Just ids_src) -> do
            -- compute new ids for el (assuming that its translation is a TupLit)
            ids_elm   <- mapM (mkIdFromType pos "tmp_el") elm_tps
            let pat_elm = TupId (map Id ids_elm) pos

            -- the assumption is pat_src is already bound in vtable!!!
            (pat_dst, bnds_dst) <- mkFullPattern (Id dst)
            body'  <- binding bnds_dst $ arr2tupExp body 
            let (_, ids_dst) = flattenPat pat_dst
            body'' <- distribLetWithExp ids_src ids_dst inds' ids_elm body' pos 

            -- check that el' is indeed a tuple literal,
            -- and enclose it in a normalized let pattern
            el'       <- arr2tupExp el
            case el' of
                TupLit {} -> distribPatExp pat_elm el' body''
                _ -> badArr2TupM $ EnablingOptError pos ("In arr2tupExp of LetWith, broken invariant: "
                                                         ++"element is not a TupLit! ") 
        (Tuple {},  Nothing) ->  
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of LetWith, broken invariant: "
                                                ++"no SymTab binding for tuple type! ")
        (_, Nothing) -> do
            el'   <- arr2tupExp el
            body' <- arr2tupExp body
            return $ LetWith dst src inds' el' body' pos
        (_, _) -> 
            badArr2TupM $ EnablingOptError pos ("In arr2tupExp of LetWith, broken invariant: "
                                                ++"SymTab binding for non-tuple type! ")

----------------------
---- Apply and If ----
----------------------

arr2tupExp (Apply "trace" [arg] _ pos) = do
    arg' <- arr2tupExp arg
    let tp' = typeOf arg'
    return $ Apply "trace" [arg'] tp' pos

arr2tupExp (Apply fnm args rtp pos) = do
    let rtp' = toTupArrType rtp
    args' <- mapM arr2tupExp args
    return $ Apply fnm args' rtp' pos

arr2tupExp (If cond e_then e_else rtp pos) = do
    let rtp' = toTupArrType rtp
    cond'   <- arr2tupExp cond
    e_then' <- arr2tupExp e_then
    e_else' <- arr2tupExp e_else
    return $ If cond' e_then' e_else' rtp' pos

-------------------------------------------------------
-------------------------------------------------------
---- Pattern Match The Rest of the Implementation! ----
----          NOT USED !!!!!                       ----
-------------------------------------------------------        
-------------------------------------------------------


arr2tupExp e = gmapM ( mkM arr2tupExp
                          `extM` arr2tupLambda
                          `extM` mapM arr2tupExp
                          `extM` mapM arr2tupExpPair ) e


arr2tupExpPair :: (Exp Type, Type) -> Arr2TupM (Exp Type, Type)
arr2tupExpPair (e,t) = do e' <- arr2tupExp e
                          return (e', toTupArrType t)

arr2tupLambda :: Lambda Type -> Arr2TupM (Lambda Type)
arr2tupLambda (AnonymFun params body rettype pos) = do  
    let params' = map toTupArrIdent params
    body' <- arr2tupAbstrFun params' body pos
    return $ AnonymFun params' body' (toTupArrType rettype) pos

arr2tupLambda (CurryFun fname exps rettype pos) = do
    exps'  <- mapM arr2tupExp exps
    return $ CurryFun fname exps' (toTupArrType rettype) pos 


-----------------------------------------------------------------
-----------------------------------------------------------------
---- HELPER FUNCTIONS                                        ----
-----------------------------------------------------------------
-----------------------------------------------------------------


---------------------------------------
---- Type transformations HELPERS  ----
---------------------------------------

toTupArrType :: Type -> Type
toTupArrType (Array tp sz u1 pos1) = 
    let tp' = toTupArrType tp
    in  case tp' of
            Tuple tps u2 pos2 -> Tuple (map (\x -> Array x sz u2 pos2) tps) u1 pos1
            _ -> Array tp' sz u1 pos1
toTupArrType (Tuple tps u pos) = 
    let tps' = concatMap (tpLift . toTupArrType) tps
    in  Tuple tps' u pos

    where 
        tpLift :: Type -> [Type]
        tpLift (Tuple ts _ _) = ts
        tpLift tp             = [tp] 
toTupArrType tp = tp


toTupArrIdent :: Ident Type -> Ident Type
toTupArrIdent idd = 
    Ident   { identName   = identName   idd
            , identType   = toTupArrType (identType idd)
            , identSrcLoc = identSrcLoc idd  
            }

flattenPat :: TupIdent Type -> (SrcLoc, [Ident Type])
flattenPat (Id    ident    ) = ( identSrcLoc ident, [ident] )
flattenPat (TupId idlst pos) = ( pos, (concat . snd . unzip . map flattenPat) idlst )

mkTupIdent :: SrcLoc -> [Ident Type] -> TupIdent Type
mkTupIdent _ [ident] = Id    ident
mkTupIdent p  idents = TupId (map Id idents) p

------------------------------------------


--------------------
--- from a potentially partially instantiated tuple id, it creates
---    a fully instantiated tuple id, i.e., the new bindings are to
---    be added to the symbol table.
--------------------
mkFullPattern :: TupIdent Type -> Arr2TupM (TupIdent Type, [(String, [Ident Type])])
mkFullPattern pat = do
    let (pos, ids) = flattenPat pat
    (ids2, bnds2) <- unzip <$> mapM processIdent ids
    let idsnew = concat ids2
    let bnds   = concat bnds2
    return ( mkTupIdent pos idsnew, bnds )

    where
        processIdent :: Ident Type -> Arr2TupM ([Ident Type], [(String, [Ident Type])])
        processIdent ident = do
            let (nm, pos) = (identName ident, identSrcLoc ident)
            case toTupArrType (identType ident) of
                Tuple tps _ _ -> do
                    idents <- mapM (mkIdFromType pos nm) tps 
                    return ( idents, [(nm, idents)] )
                tp -> if tp == identType ident
                      then return ([ident], [])
                      else badArr2TupM $ EnablingOptError pos
                                                ("in ArrTup2TupArr.hs, processIdent, non-tuple type "
                                                 ++" does not match original ident type!")
                --_             -> return ([ident], [])


mkIdFromType :: SrcLoc -> String -> Type ->
                Arr2TupM (Ident Type)
mkIdFromType pos nm t =
    if invalidType t 
    then badArr2TupM $ EnablingOptError pos 
                        ("in ArrTup2TupArr.hs, mkIdFromType "
                         ++" called on unacceptable type")
    else do tmp_nm <- new nm 
            return Ident { identName = tmp_nm
                         , identType = t
                         , identSrcLoc = pos  }

invalidType :: Type -> Bool
invalidType (Tuple {}      ) = True
invalidType (Array tp _ _ _) = invalidType tp
invalidType _                = False

--------------------------------------------------
---- Helper for function declaration / lambda ----
--------------------------------------------------
arr2tupAbstrFun :: [Ident Type] -> Exp Type -> SrcLoc -> Arr2TupM (Exp Type)
arr2tupAbstrFun args body pos = do
    let tups = filter isTuple args
    let vars = map Var tups
    resms <- mapM (mkFullPattern . Id) tups
    let (pats, bndlst)  = unzip resms 
    let bnds = concat bndlst
    body'  <- binding bnds $ arr2tupExp body
    mergePatterns (reverse pats) (reverse vars) body'

    where    
        mergePatterns :: [TupIdent Type] -> [Exp Type] -> Exp Type -> Arr2TupM (Exp Type)
        mergePatterns [] [] bdy = return bdy
        mergePatterns [] _  _   = 
            badArr2TupM $ EnablingOptError pos
                                           ("in ArrTup2TupArr.hs, mergePatterns: "
                                            ++" lengths of tups and exps don't agree!")
        mergePatterns _  [] _   = 
            badArr2TupM $ EnablingOptError pos 
                                           ("in ArrTup2TupArr.hs, mergePatterns: "
                                            ++" lengths of tups and exps don't agree!")
        mergePatterns (pat:pats) (e:es) bdy =
            mergePatterns pats es (LetPat pat e bdy pos)


        isTuple :: Ident Type -> Bool
        isTuple x = case identType x of
                        Tuple {} -> True
                        _        -> False


--------------------------------------------------------
--- Flattening a let-pattern, i.e., originally:      ---
---   let (x,y,z) = (e1, e2, e3) in body             ---
--- becomes:                                         ---
---   let x = e in let y = e2 in let z = e3 in body  ---
--------------------------------------------------------

distribPatExp :: TupIdent Type -> Exp Type -> Exp Type -> Arr2TupM (Exp Type)

distribPatExp pat@(Id idd) e body =
    return $ LetPat pat e body (identSrcLoc idd)

distribPatExp pat@(TupId idlst pos) e body =
    case e of
        TupLit es epos
            -- sanity check!
          | length idlst /= length es ->
            badArr2TupM $ EnablingOptError pos ("In ArrTup2TupArr, distribPatExp, broken invariant: "
                                                ++" the lengths of TupleLit and TupId differ! exp: "
                                                    ++ppExp 0 e++" tupid: "++ppTupId pat )
          | length idlst == 1 ->
            distribPatExp (head idlst) (head es) body
          | otherwise -> do
             body' <- distribPatExp (TupId (tail idlst) pos) (TupLit (tail es) epos) body
             distribPatExp (head idlst) (head es) body'
        _ -> return $ LetPat pat e body pos


-------------------------------------
--- Flattening a let-with Pattern ---
-------------------------------------

distribLetWithExp :: [Ident Type] -> [Ident Type] -> 
                     [Exp Type]   -> [Ident Type] -> 
                     Exp Type     -> SrcLoc       -> Arr2TupM (Exp Type)

distribLetWithExp [src] [dst] inds [elm] body pos =
    return $ LetWith src dst inds (Var elm) body pos --(identSrcLoc src)

distribLetWithExp ids_src ids_dst inds ids_elm body pos =
    -- sanity check
    let (sz1, sz2, sz3) = (length ids_src, length ids_dst, length ids_elm)
    in if sz1 > 0 && sz1 == sz2 && sz2 == sz3
       then do body' <- distribLetWithExp (tail ids_src) (tail ids_dst) inds (tail ids_elm) body pos
               distribLetWithExp [head ids_src] [head ids_dst] inds [head ids_elm] body' pos
       else badArr2TupM $ EnablingOptError pos 
                                           ("In ArrTup2TupArr, distribLetWithExp, broken invariant: "
                                            ++" the lengths of TupIds of src, dst and elms differ! ")

----------------------------------------------------
--- tupArrToLstArr: transforms a flattened tuple ---
---    of arrays into a list of array expressions---
---    and also checks that each array type does ---
---    not contain an inner tuple                ---
--- tupArrToLstArr is used in SOAC2's implem     ---
----------------------------------------------------

tupArrToLstArr :: Exp Type -> Arr2TupM [Exp Type]
tupArrToLstArr (TupLit lst pos) = do
    let lsttps = map typeOf lst
    if and $ zipWith (&&) (map isArrayType lsttps) (map (not . invalidType) lsttps)
    then return lst
    else badArr2TupM $ EnablingOptError pos 
                                        ("In ArrTup2TupArr, tupArrToLstArr, broken invariant: "
                                         ++"tuplit elems either not arrays or contain tuples! ")
tupArrToLstArr arr = do 
    let tp = typeOf arr 
    if isArrayType tp && not (invalidType tp)
    then return [arr]
    else badArr2TupM $ EnablingOptError (SrcLoc (locOf arr)) 
                                        ("In ArrTup2TupArr, tupArrToLstArr, broken invariant: "
                                         ++"argument either not an array or contains tuples! ")

isArrayType :: Type -> Bool
isArrayType (Array {}) = True
isArrayType _          = False


elemType :: Type -> Arr2TupM Type
elemType (Array t _ _ _) = return t
elemType t = badArr2TupM $ EnablingOptError 
                            (srclocOf t) 
                            ("In ArrTup2TupArr, elemType, Type of "++
                             "expression is not array, but " ++ ppType t ++ ".")

----------------------------------------------------
--- flattenTups: builds a flat tuple encompassing---
---    its expression arguments.   The first arg ---
---    is morally a tuple, i.e., either a TupVal ---
---    or a TupLit. If the first argument is a   ---
---    TupLit then the result is a TupLit.       ---
--- If the first arg is a TupVal then the result ---
---    is either a TupVal, i.e., in case the snd ---
---    argument is a value, or a TupLit otherwise---
--- flattenTups is to be used with fold for the  ---
---    purpose of flatenning an arbitrary tuple. ---
----------------------------------------------------

flattenTups :: Exp Type -> Exp Type -> Arr2TupM (Exp Type)

flattenTups (TupLit tups1 pos) (TupLit tups2 _) =
    return $ TupLit (tups1++tups2) pos

flattenTups (TupLit tups1 pos) (Literal (TupVal tupsv2) _) = do
    let tups2 = map (`Literal` pos) tupsv2
    return $ TupLit (tups1++tups2) pos

flattenTups (Literal (TupVal tupsv1) pos) (TupLit tups2 _) = do
    let tups1 = map (`Literal` pos) tupsv1
    return $ TupLit (tups1++tups2) pos

flattenTups (Literal (TupVal tups1) loc) (Literal (TupVal tups2) _) =
    return $ Literal (TupVal (tups1++tups2)) loc

flattenTups (TupLit tups1 pos) e =
    return $ TupLit (tups1++[e]) pos

flattenTups (Literal (TupVal tups1) pos) (Literal v _) =
    return $ Literal (TupVal (tups1++[v])) pos

flattenTups (Literal (TupVal tupsv1) pos) e = do
    let tups1 = map (`Literal` pos) tupsv1
    return $ TupLit (tups1++[e]) pos

flattenTups arg1 _ = 
    badArr2TupM $ EnablingOptError (SrcLoc (locOf arg1)) 
                                   ("In ArrTup2TupArr, flattenTups, broken invariant: "
                                    ++"first argument not a TupVal or a TupLit ! ")


