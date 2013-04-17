{-# LANGUAGE GeneralizedNewtypeDeriving, ScopedTypeVariables #-}

module L0.EnablingOpts.CopyCtPropFold ( 
                                copyCtProp
                            )
  where
 
import Control.Applicative
import Control.Monad.Reader
import Control.Monad.Writer

--import Data.Either

--import Control.Monad.State
import Data.Data
import Data.Generics
import Data.Array
import Data.List

import Data.Bits

import qualified Data.Map as M

import L0.AbSyn
 
import L0.EnablingOpts.EnablingOptErrors
import qualified L0.Interpreter as Interp
import L0.EnablingOpts.InliningDeadFun

--import Debug.Trace
-----------------------------------------------------------------
-----------------------------------------------------------------
---- Copy and Constant Propagation + Constant Folding        ----
-----------------------------------------------------------------
-----------------------------------------------------------------

-----------------------------------------------
-- The data to be stored in vtable           --
--   the third param (Bool) indicates if the -- 
--   binding is to be removed from program   --
-----------------------------------------------
data CtOrId tf  = Constant Value   tf Bool
                -- value for constant propagation

                | VarId    String  tf Bool
                -- Variable id for copy propagation

                | SymArr  (Exp tf) tf Bool
                -- various other opportunities for copy
                -- propagation, for the moment: (i) an indexed variable,
                -- (ii) an iota array, (iii) a replicated array, (iv) a TupLit, 
                -- and (v) an ArrayLit.   I leave this one open, i.e., (Exp tf),
                -- as I do not know exactly what we need here
                -- To Cosmin: Clean it up in the end, i.e., get rid of (Exp tf).
 
data CPropEnv tf = CopyPropEnv {   
                        envVtable  :: M.Map String (CtOrId tf),
                        program    :: Prog tf,
                        call_graph :: CallGraph
                  }

data CPropRes tf = CPropRes {
    resSuccess :: Bool
  -- ^ Whether we have changed something.
  , resNonRemovable :: [String]
  -- ^ The set of variables used as merge variables.
  }


instance Monoid (CPropRes tf) where
  CPropRes c1 m1 `mappend` CPropRes c2 m2 =
    CPropRes (c1 || c2) (m1 `union` m2)
  mempty = CPropRes False []

newtype CPropM tf a = CPropM (WriterT (CPropRes tf) (ReaderT (CPropEnv tf) (Either EnablingOptError)) a)
    deriving (MonadWriter (CPropRes tf),
              MonadReader (CPropEnv tf), Monad, Applicative, Functor)

-- | We changed part of the AST, and this is the result.  For
-- convenience, use this instead of 'return'.
changed :: a -> CPropM tf a
changed x = do
  tell $ CPropRes True []
  return x


-- | This name was used as a merge variable.
nonRemovable :: String -> CPropM tf ()
nonRemovable name = do
  tell $ CPropRes False [name]


-- | @collectNonRemovable mvars m@ executes the action @m@.  The
-- intersection of @mvars@ and any variables used as merge variables
-- while executing @m@ will also be returned, and removed from the
-- writer result.  The latter property is only important if names are
-- not unique.
collectNonRemovable :: [String] -> CPropM tf a -> CPropM tf (a, [String])
collectNonRemovable mvars m = pass collect
  where collect = do
          (x,res) <- listen m
          return ((x, mvars `intersect` resNonRemovable res),
                  const $ res { resNonRemovable = resNonRemovable res \\ mvars})


-- | The enabling optimizations run in this monad.  Note that it has no mutable
-- state, but merely keeps track of current bindings in a 'TypeEnv'.
-- The 'Either' monad is used for error handling.
runCPropM :: CPropM tf a -> CPropEnv tf -> Either EnablingOptError (a, CPropRes tf)
runCPropM  (CPropM a) env = runReaderT (runWriterT a) env

badCPropM :: EnablingOptError -> CPropM tf a
badCPropM = CPropM . lift . lift . Left


-- | Bind a name as a common (non-merge) variable.
-- TypeBox tf => 
bindVar :: CPropEnv tf -> (String, CtOrId tf) -> CPropEnv tf
bindVar env (name,val) =
  env { envVtable = M.insert name val $ envVtable env }

bindVars :: CPropEnv tf -> [(String, CtOrId tf)] -> CPropEnv tf
bindVars = foldl bindVar

binding :: [(String, CtOrId tf)] -> CPropM tf a -> CPropM tf a
binding bnds = local (`bindVars` bnds)

-- | Remove the binding for a name.
-- TypeBox tf =>
{- 
remVar :: CPropEnv tf -> String -> CPropEnv tf
remVar env name = env { envVtable = M.delete name $ envVtable env }

remVars :: CPropEnv tf -> [String] -> CPropEnv tf
remVars = foldl remVar

remBindings :: [String] -> CPropM tf a -> CPropM tf a
remBindings keys = local (`remVars` keys)
-}
-- | Applies Copy/Constant Propagation and Folding to an Entire Program.
-- TypeBox tf => 
copyCtProp :: Prog Type -> Either EnablingOptError (Bool, Prog Type)
copyCtProp prog = do
    -- buildCG :: TypeBox tf => Prog tf -> Either EnablingOptError CallGraph
    cg <- buildCG prog
    let env = CopyPropEnv { envVtable = M.empty, program = prog, call_graph = cg }
    -- res   <- runCPropM (mapM copyCtPropFun prog) env
    -- let (bs, rs) = unzip res
    (rs, res) <- runCPropM (mapM copyCtPropFun prog) env
    return (resSuccess res, rs)

copyCtPropFun :: FunDec Type -> CPropM Type (FunDec Type)
copyCtPropFun (fname, rettype, args, body, pos) = do
    body' <- copyCtPropExp body
    return (fname, rettype, args, body', pos)

--------------------------------------------------------------------
--------------------------------------------------------------------
---- Main Function: Copy/Ct propagation and folding for exps    ----
--------------------------------------------------------------------
--------------------------------------------------------------------

copyCtPropExp :: Exp Type -> CPropM Type (Exp Type)

copyCtPropExp (LetWith nm src inds el body pos) = do
    nonRemovable $ identName src
    el'       <- copyCtPropExp el
    inds'     <- mapM copyCtPropExp inds
    body'     <- copyCtPropExp body
    return $ LetWith nm src inds' el' body' pos

copyCtPropExp (LetPat pat e body pos) = do
    e'    <- copyCtPropExp e
    remv  <- isRemovablePat pat e'
    bnds  <- getPropBnds pat e' remv

    (body', mvars) <-  collectNonRemovable (map fst bnds) $
                       if null bnds then copyCtPropExp body
                       else binding bnds $ copyCtPropExp body
    if remv && null mvars then changed body'
    else return $ LetPat pat e' body' pos


copyCtPropExp (DoLoop mergepat mergeexp idd n loopbdy letbdy pos) = do
    mergeexp'    <- copyCtPropExp mergeexp
    n'       <- copyCtPropExp n
    loopbdy' <- copyCtPropExp loopbdy
    letbdy'  <- copyCtPropExp letbdy
    return $ DoLoop mergepat mergeexp' idd n' loopbdy' letbdy' pos
    
{- 
copyCtPropExp (DoLoop ind n body mergevars pos) = do
    n'    <- copyCtPropExp n
    let mergenames = map identName mergevars
    mapM_ nonRemovable mergenames
    bnds  <- mapM (\vnm -> asks $ M.lookup vnm . envVtable) mergenames
    let idbnds1 = zip bnds mergevars
    let idbnds  = filter ( \(x,_) -> isValidBnd     x ) idbnds1
    let remkeys = map (\(_, (Ident s _ _) ) -> s) idbnds
    body' <- remBindings remkeys $ copyCtPropExp body
    let newloop = DoLoop ind n' body' mergevars pos
    return newloop 
    where
        isValidBnd :: Maybe (CtOrId tf) -> Bool
        isValidBnd bnd = case bnd of
                            Nothing -> False
                            Just _  -> True
-}

copyCtPropExp e@(Var (Ident vnm _ pos)) = do 
    -- let _ = trace ("In VarExp: "++ppExp 0 e) e
    bnd <- asks $ M.lookup vnm . envVtable
    case bnd of
        Nothing                 -> return e
        Just (Constant v   _ _) -> if isBasicTypeVal v 
                                   then changed $ Literal v 
                                   else return e
        Just (VarId  id' tp1 _) -> changed $ Var (Ident id' tp1 pos) -- or tp
        Just (SymArr e'    _ _) ->
            case e' of
                Replicate _ _ _   -> return e
                TupLit    _ _     -> if isCtOrCopy e then changed e' else return e
                ArrayLit  _ _ _   -> return e
                Index _ _ _ _ _   -> changed e'
                -- DO NOT INLINE IOTA!
                Iota  _ _         -> changed e'
                --Iota _ _          -> return e
                _                 -> return e

copyCtPropExp eee@(Index idd@(Ident vnm tp p) inds tp1 tp2 pos) = do 
  inds' <- mapM copyCtPropExp inds
  bnd   <- asks $ M.lookup vnm . envVtable 
  case bnd of
    Nothing               -> return  $ Index idd inds' tp1 tp2 pos
    Just (VarId  id' _ _) -> changed $ Index (Ident id' tp p) inds' tp1 tp2 pos
    Just (Constant v _ _) -> 
      case v of
        ArrayVal _ _ _ ->
          let sh = arrayShape v 
          in case ctIndex inds' of
               Nothing -> return $ Index idd inds' tp1 tp2 pos
               Just iis-> 
                 if (length iis == length sh)
                 then case getArrValInd v iis of
                        Nothing -> return $ Index idd inds' tp1 tp2 pos
                        Just el -> changed $ Literal el
                 else return $ Index idd inds' tp1 tp2 pos
        _ -> badCPropM $ TypeError pos  " indexing into a non-array value "
    Just (SymArr e' _ _) -> 
      case (e', inds') of 
        (Iota _ _, [ii]) -> changed ii
        (Iota _ _, _)    -> badCPropM $ TypeError pos  " bad indexing in iota "

        (Index aa ais t1 _ _,_) -> do
            -- the array element type is the same as the one of the big array, i.e., t1
            -- the result type is the same as eee's, i.e., tp2
            inner <- copyCtPropExp( Index aa (ais ++ inds') t1 tp2 pos ) 
            changed inner

        (ArrayLit _ _ _   , _) ->
            case ctIndex inds' of
                Nothing  -> return $ Index idd inds' tp1 tp2 pos
                Just iis -> case getArrLitInd e' iis of
                                Nothing -> return $ Index idd inds' tp1 tp2 pos
                                Just el -> changed el

        (TupLit   _ _, _       ) -> badCPropM $ TypeError pos  " indexing into a tuple "


        (Replicate _ vvv@(Var vv@(Ident _ _ _)) _, _:is') -> do
            inner <- if null is' 
                     then copyCtPropExp vvv
                     else let tp1' = stripArray 1 (identType vv) 
                          in copyCtPropExp (Index vv is' tp1' tp2 pos) -- copyCtPropExp (Index vv is' tp1 tp2 pos) 
            changed inner
        (Replicate _ (Index a ais _ _ _) _, _:is') -> do
            inner <- copyCtPropExp (Index a (ais ++ is') tp1 tp2 pos)
            changed inner
        (Replicate _ (Literal arr@(ArrayVal _ _ _)) _, _:is') -> do 
            case ctIndex is' of
                Nothing -> return $ Index idd inds' tp1 tp2 pos
                Just iis-> case getArrValInd arr iis of 
                               Nothing -> return $ Index idd inds' tp1 tp2 pos
                               Just el -> changed $ Literal el
        (Replicate _ val@(Literal _) _, _:is') -> do
            if null is' then changed val
            else badCPropM $ TypeError pos  " indexing into a basic type "

        (Replicate _ arr@(ArrayLit _ _ _) _, _:is') -> do
            case ctIndex is' of
                Nothing -> return $ Index idd inds' tp1 tp2 pos
                Just iis-> case getArrLitInd arr iis of 
                               Nothing -> return $ Index idd inds' tp1 tp2 pos
                               Just el -> changed el
        (Replicate _ tup@(TupLit _ _) _, _:is') -> do
            if null is' && isCtOrCopy tup then changed $ tup
            else  badCPropM $ TypeError pos  " indexing into a tuple "
        (Replicate _ (Iota n _) _, _:is') -> do
            if     (length is' == 0) then changed $ Iota n pos 
            else if(length is' == 1) then changed $ head is'
            else badCPropM $ TypeError pos  (" illegal indexing: " ++ ppExp 0 eee)
        (Replicate _ _ _, _) -> 
            return $ Index idd inds' tp1 tp2 pos

        _ -> badCPropM $ CopyCtPropError pos (" Unreachable case in copyCtPropExp of Index exp: " ++
                                              ppExp 0 eee++" is bound to "++ppExp 0 e' ) --e 
                                              --" index-exp of "++ppExp 0 eee++" bound to "++ppExp 0 e' ) --e

copyCtPropExp (BinOp bop e1 e2 tp pos) = do
    e1'   <- copyCtPropExp e1
    e2'   <- copyCtPropExp e2
    ctFoldBinOp (BinOp bop e1' e2' tp pos)

copyCtPropExp (And e1 e2 pos) = do
    e1'   <- copyCtPropExp e1
    e2'   <- copyCtPropExp e2
    ctFoldBinOp (And e1' e2' pos)

copyCtPropExp (Or e1 e2 pos) = do
    e1'   <- copyCtPropExp e1
    e2'   <- copyCtPropExp e2
    ctFoldBinOp $ Or e1' e2' pos

copyCtPropExp (Negate e tp pos) = do
    e'   <- copyCtPropExp e
    if( isValue e' ) 
    then case e' of
            Literal (IntVal  v _) -> changed $ Literal (IntVal  (0  -v) pos)
            Literal (RealVal v _) -> changed $ Literal (RealVal (0.0-v) pos)
            _ -> badCPropM $ TypeError pos  " ~ operands not of (the same) numeral type! "
    else return $ Negate e' tp pos

copyCtPropExp (Not e pos) = do 
    e'   <- copyCtPropExp e
    if( isValue e' ) 
    then case e' of
            Literal (LogVal  v _) -> changed $ Literal (LogVal (not v) pos)
            _ -> badCPropM $ TypeError pos  " not operands not of (the same) numeral type! "    
    else return $ Not e' pos

copyCtPropExp (If e1 e2 e3 tp pos) = do 
    e1' <- copyCtPropExp e1
    e2' <- copyCtPropExp e2
    e3' <- copyCtPropExp e3
    if      isCt1 e1' then changed e2'
    else if isCt0 e1' then changed e3'
    else return $ If e1' e2' e3' tp pos

-----------------------------------------------------------
--- If expression is an array literal than replace it   ---
---    with the array's size                            ---
-----------------------------------------------------------
copyCtPropExp (Size e pos) = do 
    e' <- copyCtPropExp e
    case e' of
        Var idd -> do
            vv <- asks $ M.lookup (identName idd) . envVtable
            case vv of
                Just (SymArr (ArrayLit   els _ _) _ _) -> 
                    changed $ Literal (IntVal (length els) pos) 
                Just (Constant (ArrayVal arr _ _) _ _) -> 
                    changed $ Literal (IntVal (length (elems arr)) pos)
                _ -> return $ Size e' pos
        ArrayLit els _ _ ->  do
            changed $ Literal (IntVal (length els) pos)
        _ ->  do return $ Size e' pos

-----------------------------------------------------------
--- If all params are values and function is free of IO ---
---    then evaluate the function call                  ---
-----------------------------------------------------------
copyCtPropExp (Apply fname args tp pos) = do
    args' <- mapM copyCtPropExp args
    cg    <- asks $ call_graph
    let has_io = case M.lookup fname cg of
                   Just (_,_,o) -> o
                   Nothing-> False
    (all_are_vals, vals) <- allArgsAreValues args' 
    res <- if all_are_vals && (not has_io)
           then do prg <- asks $ program
                   let vv = Interp.runFun fname vals  prg
                   case vv of 
                       Just (Right v) -> changed $ Literal v
                       _ -> badCPropM $ EnablingOptError pos (" Interpreting fun " ++ 
                                                              fname ++ " yields error!")
           else do return $ Apply fname args' tp pos
    return res

    where 
        allArgsAreValues :: [Exp Type] -> CPropM Type (Bool, [Value])
        allArgsAreValues []     = do return (True, [])
        allArgsAreValues (a:as) = 
            case a of
                Literal v -> do (res, vals) <- allArgsAreValues as
                                if res then do return (True,  v:vals)
                                       else do return (False, []    )
                Var idd   -> do vv <- asks $ M.lookup (identName idd) . envVtable
                                case vv of
                                  Just (Constant v _ _) -> do
                                    (res, vals) <- allArgsAreValues as
                                    if res then return (True,  v:vals)
                                           else return (False, []    )
                                  _ -> do return (False, [])
                _         -> do return (False, [])
------------------------------
--- Pattern Match the Rest ---
------------------------------

copyCtPropExp e = gmapM (mkM copyCtPropExp
                         `extM` copyCtPropLambda
                         `extM` mapM copyCtPropExp
                         `extM` mapM copyCtPropExpPair) e

copyCtPropExpPair :: (Exp Type, Type) -> CPropM Type (Exp Type, Type)
copyCtPropExpPair (e, t) = do
  e' <- copyCtPropExp e
  return (e', t)

-- data Lambda ty = AnonymFun [Ident Type] (Exp ty) Type SrcLoc
--                    -- fn int (bool x, char z) => if(x) then ord(z) else ord(z)+1 *)
--               | CurryFun String [Exp ty] ty SrcLoc
--                    -- op +(4) *)
--                 deriving (Eq, Ord, Typeable, Data, Show)

copyCtPropLambda :: Lambda Type -> CPropM Type (Lambda Type)
copyCtPropLambda (AnonymFun ids body tp pos) = do
    body' <- copyCtPropExp body
    return $ AnonymFun ids body' tp pos
copyCtPropLambda (CurryFun fname params tp pos) = do
    params' <- copyCtPropExpList params
    return $ CurryFun fname params' tp pos

    


copyCtPropExpList :: [Exp Type] -> CPropM Type [Exp Type]
copyCtPropExpList es = mapM copyCtPropExp es

------------------------------------------------
---- Constant Folding                       ----
------------------------------------------------

ctFoldBinOp :: Exp Type -> CPropM Type (Exp Type)
ctFoldBinOp e@(BinOp Plus e1 e2 _ pos) = do
    if isCt0 e1 then changed e2 else if isCt0 e2 then changed e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (v1+v2) pos)
                (Literal (RealVal v1 _), Literal (RealVal v2 _)) -> changed $ Literal (RealVal (v1+v2) pos)
                _ -> badCPropM $ TypeError pos  " + operands not of (the same) numeral type! "
         else return e
ctFoldBinOp e@(BinOp Minus e1 e2 _ pos) = do
    if isCt0 e2 then changed e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (v1-v2) pos)
                (Literal (RealVal v1 _), Literal (RealVal v2 _)) -> changed $ Literal (RealVal (v1-v2) pos)
                _ -> badCPropM $ TypeError pos  " - operands not of (the same) numeral type! "
         else return e
ctFoldBinOp e@(BinOp Times e1 e2 _ pos) = do
    if      isCt0 e1 then changed e1 else if isCt0 e2 then changed e2
    else if isCt1 e1 then changed e2 else if isCt1 e2 then changed e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (v1*v2) pos)
                (Literal (RealVal v1 _), Literal (RealVal v2 _)) -> changed $ Literal (RealVal (v1*v2) pos)
                _ -> badCPropM $ TypeError pos  " * operands not of (the same) numeral type! "
         else return e
ctFoldBinOp e@(BinOp Divide e1 e2 _ pos) = do
    if      isCt0 e1 then changed e1
    else if isCt0 e2 then badCPropM $ Div0Error pos
    else if isCt1 e2 then changed e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (div v1 v2) pos)
                (Literal (RealVal v1 _), Literal (RealVal v2 _)) -> changed $ Literal (RealVal (v1 / v2)   pos)
                _ -> badCPropM $ TypeError pos  " / operands not of (the same) numeral type! "
         else return e
ctFoldBinOp e@(BinOp Pow e1 e2 _ pos) = do
    if      isCt0 e1 || isCt1 e1 || isCt1 e2 then changed e1
    else if isCt0 e2 then case e1 of
                            Literal (IntVal  _ _) -> changed $ Literal (IntVal  1   pos)
                            Literal (RealVal _ _) -> changed $ Literal (RealVal 1.0 pos)
                            _ -> badCPropM $ TypeError pos  " pow operands not of (the same) numeral type! "
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (v1 ^v2) pos)
                (Literal (RealVal v1 _), Literal (RealVal v2 _)) -> changed $ Literal (RealVal (v1**v2) pos)
                _ -> badCPropM $ TypeError pos  " pow operands not of (the same) numeral type! "
         else return e
ctFoldBinOp e@(BinOp ShiftL e1 e2 _ pos) = do
    if      isCt0 e2 then changed e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (shiftL v1 v2) pos)
                _ -> badCPropM $ TypeError pos  " << operands not of integer type! "
         else return e
ctFoldBinOp e@(BinOp ShiftR e1 e2 _ pos) = do
    if      isCt0 e2 then changed e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (shiftR v1 v2) pos)
                _ -> badCPropM $ TypeError pos  " >> operands not of integer type! "
         else return e
ctFoldBinOp e@(BinOp Band e1 e2 _ pos) = do
    if      isCt0 e1 then changed e1 else if isCt0 e2 then changed e2
    else if isCt1 e1 then changed e2 else if isCt1 e2 then changed e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (v1 .&. v2) pos)
                _ -> badCPropM $ TypeError pos  " & operands not of integer type! "
         else return e
ctFoldBinOp e@(BinOp Bor e1 e2 _ pos) = do
    if      isCt0 e1 then changed e2 else if isCt0 e2 then changed e1
    else if isCt1 e1 then changed e1 else if isCt1 e2 then changed e2
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (v1 .|. v2) pos)
                _ -> badCPropM $ TypeError pos  " | operands not of integer type! "
         else return e
ctFoldBinOp e@(BinOp Xor e1 e2 _ pos) = do
    if      isCt0 e1 then changed e2 else if isCt0 e2 then return e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (IntVal  (xor v1 v2) pos)
                _ -> badCPropM $ TypeError pos  " ^ operands not of integer type! "
         else return e
ctFoldBinOp e@(And e1 e2 pos) = do
    if      isCt0 e1 then changed e1 else if isCt0 e2 then changed e2
    else if isCt1 e1 then changed e2 else if isCt1 e2 then changed e1
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (LogVal  v1 _), Literal (LogVal  v2 _)) -> changed $ Literal (LogVal  (v1 && v2) pos)
                _ -> badCPropM $ TypeError pos  " && operands not of boolean type! "
         else return e
ctFoldBinOp e@(Or e1 e2 pos) = do
    if      isCt0 e1 then changed e2 else if isCt0 e2 then changed e1
    else if isCt1 e1 then changed e1 else if isCt1 e2 then changed e2
    else if(isValue e1 && isValue e2)
         then case (e1, e2) of
                (Literal (LogVal  v1 _), Literal (LogVal  v2 _)) -> changed $ Literal (LogVal  (v1 || v2) pos)
                _ -> badCPropM $ TypeError pos  " || operands not of boolean type! "
         else return e

ctFoldBinOp e@(BinOp Equal e1 e2 _ pos) = do
    if(isValue e1 && isValue e2) then
      case (e1, e2) of
        -- for numerals we could build node e1-e2, simplify and test equality with 0 or 0.0!
        (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (LogVal (v1==v2) pos)
        (Literal (RealVal v1 _), Literal (RealVal v2 _)) -> changed $ Literal (LogVal (v1==v2) pos)
        (Literal (LogVal  v1 _), Literal (LogVal  v2 _)) -> changed $ Literal (LogVal (v1==v2) pos)
        (Literal (CharVal v1 _), Literal (CharVal v2 _)) -> changed $ Literal (LogVal (v1==v2) pos)
        --(Literal (TupVal  v1 _), Literal (TupVal  v2 _)) -> return (True, Literal (LogVal (v1==v2) pos))
        _ -> badCPropM $ TypeError pos  " equal operands not of (the same) basic type! "
    else return e
ctFoldBinOp e@(BinOp Less e1 e2 _ pos) = do
    if(isValue e1 && isValue e2) then
      case (e1, e2) of
        -- for numerals we could build node e1-e2, simplify and compare with 0 or 0.0!
        (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (LogVal (v1<v2) pos)
        (Literal (RealVal v1 _), Literal (RealVal v2 _)) -> changed $ Literal (LogVal (v1<v2) pos)
        (Literal (LogVal  v1 _), Literal (LogVal  v2 _)) -> changed $ Literal (LogVal (v1<v2) pos)
        (Literal (CharVal v1 _), Literal (CharVal v2 _)) -> changed $ Literal (LogVal (v1<v2) pos)
        --(Literal (TupVal  v1 _), Literal (TupVal  v2 _)) -> return (True, Literal (LogVal (v1<v2) pos))
        _ -> badCPropM $ TypeError pos  " less-than operands not of (the same) basic type! "
    else return e
ctFoldBinOp e@(BinOp Leq e1 e2 _ pos) = do
    if(isValue e1 && isValue e2) then
      case (e1, e2) of
        -- for numerals we could build node e1-e2, simplify and compare with 0 or 0.0!
        (Literal (IntVal  v1 _), Literal (IntVal  v2 _)) -> changed $ Literal (LogVal (v1<=v2) pos)
        (Literal (RealVal v1 _), Literal (RealVal v2 _)) -> changed $ Literal (LogVal (v1<=v2) pos)
        (Literal (LogVal  v1 _), Literal (LogVal  v2 _)) -> changed $ Literal (LogVal (v1<=v2) pos)
        (Literal (CharVal v1 _), Literal (CharVal v2 _)) -> changed $ Literal (LogVal (v1<=v2) pos)
        --(Literal (TupVal  v1 _), Literal (TupVal  v2 _)) -> return (True, Literal (LogVal (v1<=v2) pos))
        _ -> badCPropM $ TypeError pos  " less-than-or-equal operands not of (the same) basic type! "
    else return e
ctFoldBinOp e = return e



----------------------------------------------------
---- Helpers for Constant Folding                ---
----------------------------------------------------


isValue :: TypeBox tf => Exp tf -> Bool
isValue e = case e of
              Literal _ -> True
              _         -> False 

isCt1 :: TypeBox tf => Exp tf -> Bool
isCt1 e = case e of
            Literal (IntVal  one _)  -> (one == 1  )
            Literal (RealVal one _)  -> (one == 1.0)
            Literal (LogVal True _)  -> True
            _                        -> False
isCt0 :: TypeBox tf => Exp tf -> Bool
isCt0 e = case e of
            Literal (IntVal  zr   _) -> (zr == 0  )
            Literal (RealVal zr   _) -> (zr == 0.0)
            Literal (LogVal False _) -> True
            _                        -> False

----------------------------------------------------
---- Helpers for Constant/Copy Propagation       ---
----------------------------------------------------

isBasicTypeVal :: Value -> Bool
isBasicTypeVal (IntVal     _ _) = True
isBasicTypeVal (RealVal    _ _) = True
isBasicTypeVal (LogVal     _ _) = True
isBasicTypeVal (CharVal    _ _) = True
isBasicTypeVal (ArrayVal _ _ _) = False
isBasicTypeVal (TupVal    vs _) = 
    foldl (&&) True (map isBasicTypeVal vs)

isCtOrCopy :: TypeBox tf => Exp tf -> Bool
isCtOrCopy (Literal  val   ) = isBasicTypeVal val
isCtOrCopy (TupLit   ts _  ) = foldl (&&) True (map isCtOrCopy ts)
isCtOrCopy (Var           _) = True
isCtOrCopy (Iota        _ _) = True
isCtOrCopy (Index _ _ _ _ _) = True
isCtOrCopy _                 = False

isRemovablePat  :: TypeBox tf => TupIdent tf -> Exp tf -> CPropM tf Bool 
isRemovablePat (Id _) e = 
 let s=case e of
        Var     _         -> True
        Index   _ _ _ _ _ -> True
        Literal v         -> isBasicTypeVal v
        TupLit  _ _       -> isCtOrCopy e     -- False
--      DO NOT INLINE IOTA
        Iota    _ _       -> True
        _                 -> False
 in return s

isRemovablePat (TupId tups _) e = 
    case e of
          Var (Ident vnm _ _)      -> do
              bnd <- asks $ M.lookup vnm . envVtable
              case bnd of
                  Just (Constant val@(TupVal ts   _) _ _) -> 
                      return ( isBasicTypeVal val && length ts == length tups )
                  Just (SymArr   tup@(TupLit ts _  ) _ _) -> 
                      return ( isCtOrCopy tup && length ts == length tups ) 
                  _ ->  return False
          TupLit  _ _              -> return (isCtOrCopy     e  )
          Literal val@(TupVal _ _) -> return (isBasicTypeVal val)
          _ -> return False

getPropBnds :: TypeBox tf => TupIdent tf -> Exp tf -> Bool -> CPropM tf [(String,CtOrId tf)]
getPropBnds ( Id (Ident var tp pos) ) e to_rem = 
  let r = case e of
            Literal v            -> [(var, (Constant v (boxType (valueType v)) to_rem))]
            Var (Ident id1 tp1 _)-> [(var, (VarId  id1 tp1 to_rem))]
            Index   _ _ _ _ _    -> [(var, (SymArr e   tp  to_rem))]
            TupLit     _  _      -> [(var, (SymArr e   tp  to_rem))]

            Iota           _ _   -> let newtp = boxType (Array (Int pos) Nothing pos) -- (Just n) does not work Exp tf
                                    in  [(var, SymArr e newtp to_rem)]
            Replicate _ _ _      -> [(var, SymArr e tp to_rem)] 
            ArrayLit    _ _ _    -> [(var, SymArr e tp to_rem)]
            _ -> [] 
  in return r 
getPropBnds pat@(TupId ids _) e to_rem = 
    case e of
        TupLit  ts _          ->
            if( length ids == length ts )
            then do lst <- mapM  (\(x,y)->getPropBnds x y to_rem) (zip ids ts)
                    return (foldl (++) [] lst)
            else return []
        Literal (TupVal ts _) ->
            if( length ids == length ts )
            then do lst <- mapM (\(x,y)->getPropBnds x (Literal y) to_rem) (zip ids ts)
                    return (foldl (++) [] lst)
            else return []
        Var (Ident vnm _ _)   -> do 
            bnd <- asks $ M.lookup vnm . envVtable
            case bnd of
                Just (SymArr tup@(TupLit   _ _) _ _) -> getPropBnds pat tup           to_rem
                Just (Constant tup@(TupVal _ _) _ _) -> getPropBnds pat (Literal tup) to_rem 
                _                                    -> return []
        _ -> return []

ctIndex :: TypeBox tf => [Exp tf] -> Maybe [Int]
ctIndex []     = Just []
ctIndex (i:is) = 
  case i of
    Literal (IntVal ii _) ->  
      let x = ctIndex is in
      case x of
        Nothing -> Nothing
        Just y -> Just (ii:y)
    _ -> Nothing 

getArrValInd :: Value -> [Int] -> Maybe Value
getArrValInd v [] = if isBasicTypeVal v then Just v else Nothing 
getArrValInd (ArrayVal arr _ _) (i:is) = getArrValInd (arr ! i) is
getArrValInd _ _ = Nothing 

getArrLitInd :: TypeBox tf => Exp tf -> [Int] -> Maybe (Exp tf)
getArrLitInd e [] = if isCtOrCopy e then Just e else Nothing 
getArrLitInd (ArrayLit els _ _) (i:is) = getArrLitInd (els !! i) is
getArrLitInd (Literal arr@(ArrayVal _ _ _)) (i:is) = 
    case getArrValInd arr (i:is) of
        Nothing -> Nothing
        Just v  -> Just (Literal v) 
getArrLitInd _ _ = Nothing 
