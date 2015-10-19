{-# LANGUAGE TypeFamilies, LambdaCase #-}
module Futhark.CodeGen.KernelImpGen
  ( compileProg
  )
  where

import Control.Monad.Except
import Control.Monad.Reader
import Control.Applicative
import Data.Maybe
import Data.Monoid
import qualified Data.HashMap.Lazy as HM
import qualified Data.HashSet as HS
import Data.List

import Prelude

import Futhark.MonadFreshNames
import Futhark.Representation.ExplicitMemory
import qualified Futhark.CodeGen.KernelImp as Imp
import Futhark.CodeGen.KernelImp (bytes)
import qualified Futhark.CodeGen.ImpGen as ImpGen
import Futhark.Analysis.ScalExp as SE
import qualified Futhark.Representation.ExplicitMemory.IndexFunction.Unsafe as IxFun
import Futhark.CodeGen.SetDefaultSpace
import Futhark.Tools (partitionChunkedLambdaParameters)

type CallKernelGen = ImpGen.ImpM Imp.CallKernel
type InKernelGen = ImpGen.ImpM Imp.InKernel

callKernelOperations :: ImpGen.Operations Imp.CallKernel
callKernelOperations =
  ImpGen.Operations { ImpGen.opsExpCompiler = kernelCompiler
                    , ImpGen.opsCopyCompiler = callKernelCopy
                    }

inKernelOperations :: ImpGen.Operations Imp.InKernel
inKernelOperations = ImpGen.defaultOperations
                     { ImpGen.opsCopyCompiler = inKernelCopy }

compileProg :: Prog -> Either String Imp.Program
compileProg = liftM (setDefaultSpace (Imp.Space "device")) .
              ImpGen.compileProg callKernelOperations
              (Imp.Space "device")

-- | Recognise kernels (maps), give everything else back.
kernelCompiler :: ImpGen.ExpCompiler Imp.CallKernel

kernelCompiler
  (ImpGen.Destination dest)
  (LoopOp (Kernel _ w global_thread_index ispace inps returns body)) = do

  kernel_size <- ImpGen.subExpToDimSize w

  let global_thread_index_param = Imp.ScalarParam global_thread_index Int
      shape = map (ImpGen.compileSubExp . snd) ispace
      indices = map fst ispace

  let indices_lparams = [ Param (Ident index $ Basic Int) Scalar | index <- indices ]
      bound_in_kernel = global_thread_index : indices ++ map kernelInputName inps
      kernel_bnds = bodyBindings body

      index_expressions = unflattenIndex shape $ Imp.ScalarVar global_thread_index
      set_indices = forM_ (zip indices index_expressions) $ \(i, x) ->
        ImpGen.emit $ Imp.SetScalar i x

      read_params = mapM_ readKernelInput inps

      perms = map snd returns
      write_result =
        sequence_ $ zipWith3 (writeThreadResult indices) perms dest $ bodyResult body

  makeAllMemoryGlobal $ do
    kernel_body <- liftM (setBodySpace $ Imp.Space "global") $
                   ImpGen.subImpM_ inKernelOperations $
                   ImpGen.withParams [global_thread_index_param] $
                   ImpGen.declaringLParams (indices_lparams++map kernelInputParam inps) $ do
                     ImpGen.comment "compute thread index" set_indices
                     ImpGen.comment "read kernel parameters" read_params
                     ImpGen.compileBindings kernel_bnds $
                      ImpGen.comment "write kernel result" write_result

    -- Compute the variables that we need to pass to and from the
    -- kernel.
    uses <- computeKernelUses dest kernel_body bound_in_kernel

    ImpGen.emit $ Imp.Op $ Imp.Kernel Imp.MapKernel {
        Imp.kernelThreadNum = global_thread_index
      , Imp.kernelBody = kernel_body
      , Imp.kernelUses = uses
      , Imp.kernelSize = kernel_size
      }
    return ImpGen.Done

kernelCompiler
  (ImpGen.Destination dest)
  (LoopOp (ReduceKernel _ _ kernel_size reduce_lam fold_lam nes _)) = do

    local_id <- newVName "local_id"
    group_id <- newVName "group_id"
    global_id <- newVName "global_id"

    (num_groups, group_size, per_thread_chunk, num_elements, _) <-
      compileKernelSize kernel_size

    let fold_lparams = lambdaParams fold_lam
        (fold_chunk_param, _) =
          partitionChunkedLambdaParameters $ lambdaParams fold_lam

        reduce_lparams = lambdaParams reduce_lam
        (other_index_param, actual_reduce_params) =
          partitionChunkedLambdaParameters $ lambdaParams reduce_lam
        (reduce_acc_params, reduce_arr_params) =
          splitAt (length nes) actual_reduce_params

        offset = paramName other_index_param

    (acc_mem_params, acc_local_mem) <-
      unzip <$> mapM (createAccMem group_size) reduce_acc_params

    (call_with_prologue, prologue) <-
      makeAllMemoryGlobal $ ImpGen.subImpM inKernelOperations $
      ImpGen.withBasicVar local_id Int $
      ImpGen.declaringBasicVar local_id Int $
      ImpGen.declaringBasicVar group_id Int $
      ImpGen.declaringBasicVar global_id Int $
      ImpGen.declaringBasicVar (lambdaIndex reduce_lam) Int $
      ImpGen.declaringBasicVar (lambdaIndex fold_lam) Int $
      ImpGen.withParams acc_mem_params $
      ImpGen.declaringLParams (fold_lparams++reduce_lparams) $ do

        ImpGen.emit $
          Imp.Op (Imp.GetLocalId local_id 0) <>
          Imp.Op (Imp.GetGroupId group_id 0) <>
          Imp.Op (Imp.GetGlobalId global_id 0) <>
          Imp.SetScalar (lambdaIndex reduce_lam) (Imp.ScalarVar global_id) <>
          Imp.SetScalar (lambdaIndex fold_lam) (Imp.ScalarVar global_id)

        reduce_acc_dest <- ImpGen.destinationFromParams reduce_acc_params

        fold_op <-
          ImpGen.subImpM_ inKernelOperations $ do
            computeThreadChunkSize
              (Imp.ScalarVar $ lambdaIndex fold_lam)
              (ImpGen.dimSizeToExp per_thread_chunk)
              (ImpGen.dimSizeToExp num_elements) $
              paramName fold_chunk_param
            ImpGen.compileBody reduce_acc_dest $ lambdaBody fold_lam

        write_fold_result <-
          ImpGen.subImpM_ inKernelOperations $
          zipWithM_ (writeFoldResult local_id) acc_local_mem reduce_acc_params

        let read_reduce_args = zipWithM_ (readReduceArgument local_id offset)
                               reduce_arr_params acc_local_mem

        reduce_op <-
          ImpGen.subImpM_ inKernelOperations $ do
            ImpGen.comment "read array element" read_reduce_args
            ImpGen.compileBody reduce_acc_dest $ lambdaBody reduce_lam

        write_result <-
          ImpGen.subImpM_ inKernelOperations $
          zipWithM_(writeFinalResult group_id) dest reduce_acc_params

        let local_mem = acc_local_mem
            bound_in_kernel = map paramName (lambdaParams fold_lam ++
                                             lambdaParams reduce_lam) ++
                              [lambdaIndex fold_lam,
                               lambdaIndex reduce_lam,
                               offset,
                               local_id,
                               group_id,
                               global_id] ++
                              map Imp.paramName acc_mem_params

        return $ \prologue -> do
          uses <- computeKernelUses dest [freeIn prologue,
                                          freeIn fold_op,
                                          freeIn write_fold_result,
                                          freeIn reduce_op,
                                          freeIn write_result
                                          ]
                  bound_in_kernel

          ImpGen.emit $ Imp.Op $ Imp.Reduce Imp.ReduceKernel
            { Imp.reductionKernelName = lambdaIndex fold_lam
            , Imp.reductionOffsetName = offset
            , Imp.reductionThreadLocalMemory = local_mem

            , Imp.reductionPrologue = prologue
            , Imp.reductionFoldOperation = fold_op
            , Imp.reductionWriteFoldResult = write_fold_result
            , Imp.reductionReduceOperation = reduce_op
            , Imp.reductionWriteFinalResult = write_result

            , Imp.reductionNumGroups = num_groups
            , Imp.reductionGroupSize = group_size

            , Imp.reductionUses = uses
            }
          return ImpGen.Done
    call_with_prologue prologue
  where createAccMem group_size param
          | Basic bt <- paramType param = do
              mem_shared <- newVName (baseString (paramName param) <> "_mem_local")
              total_size <- newVName "total_size"
              ImpGen.emit $
                Imp.DeclareScalar total_size Int
              ImpGen.emit $
                Imp.SetScalar total_size $
                Imp.SizeOf bt * Imp.innerExp (ImpGen.dimSizeToExp group_size)
              return (Imp.MemParam mem_shared (Imp.VarSize total_size) $ Space "local",
                      (mem_shared, Imp.VarSize total_size))
          | Array {} <- paramType param,
            MemSummary mem _ <- paramLore param = do
              mem_size <-
                ImpGen.entryMemSize <$> ImpGen.lookupMemory mem
              return (Imp.MemParam mem mem_size $ Space "local",
                      (mem, mem_size))
          | otherwise =
            fail $ "createAccMem: cannot deal with accumulator param " ++
            pretty param

        writeFoldResult local_id (mem, _) param
          | Basic _ <- paramType param =
              ImpGen.emit $
              Imp.Write mem (bytes i) bt (Space "local") $
              Imp.ScalarVar (paramName param)
          | otherwise =
              return ()
          where bt = elemType $ paramType param
                i = Imp.ScalarVar local_id * Imp.SizeOf bt

        readReduceArgument local_id offset param (mem, _)
          | Basic _ <- paramType param =
              ImpGen.emit $
                Imp.SetScalar (paramName param) $
                Imp.Index mem (bytes i) bt (Space "local")
          | otherwise =
              return ()
          where i = (Imp.ScalarVar local_id + Imp.ScalarVar offset) * Imp.SizeOf bt
                bt = elemType $ paramType param

        writeFinalResult group_id (ImpGen.ArrayDestination memloc _) acc_param
          | ImpGen.CopyIntoMemory (ImpGen.MemLocation out_arr_mem out_shape ixfun) <- memloc = do
              let target =
                    case arrayDims $ paramType acc_param of
                      [] ->
                        ImpGen.ArrayElemDestination
                        out_arr_mem bt (Imp.Space "global") $
                        Imp.bytes $ Imp.SizeOf bt * Imp.ScalarVar group_id
                      ds ->
                        let destloc = ImpGen.MemLocation out_arr_mem (drop 1 out_shape) $
                                      IxFun.applyInd ixfun [ImpGen.varIndex group_id]
                        in ImpGen.ArrayDestination (ImpGen.CopyIntoMemory destloc) $
                           map (const Nothing) ds
              ImpGen.compileResultSubExp target $ Var $ paramName acc_param
          where bt = elemType $ paramType acc_param
        writeFinalResult _ _ _ =
          fail "writeFinalResult: invalid destination"


-- We generate a simple kernel for itoa and replicate.
kernelCompiler target (PrimOp (Iota n)) = do
  i <- newVName "i"
  global_thread_index <- newVName "global_thread_index"
  kernelCompiler target $
    LoopOp $ Kernel [] n global_thread_index [(i,n)] [] [(Basic Int,[0])] (Body () [] [Var i])
kernelCompiler target (PrimOp (Replicate n v)) = do
  i <- newVName "i"
  global_thread_index <- newVName "global_thread_index"
  t <- subExpType v
  kernelCompiler target $
    LoopOp $ Kernel [] n global_thread_index [(i,n)] [] [(t,[0..arrayRank t])] (Body () [] [v])

-- Allocation in the "local" space is just a placeholder.
kernelCompiler _ (PrimOp (Alloc _ (Space "local"))) =
  return ImpGen.Done

kernelCompiler _ e =
  return $ ImpGen.CompileExp e

compileKernelSize :: KernelSize
                  -> ImpGen.ImpM op (Imp.DimSize, Imp.DimSize, Imp.DimSize, Imp.DimSize, Imp.DimSize)
compileKernelSize (KernelSize num_groups group_size
                   per_thread_elements num_elements offset_multiple) = do
  num_groups' <- ImpGen.subExpToDimSize num_groups
  group_size' <- ImpGen.subExpToDimSize group_size
  per_thread_elements' <- ImpGen.subExpToDimSize per_thread_elements
  num_elements' <- ImpGen.subExpToDimSize num_elements
  offset_multiple' <- ImpGen.subExpToDimSize offset_multiple
  return (num_groups', group_size', per_thread_elements', num_elements', offset_multiple')

callKernelCopy :: ImpGen.CopyCompiler Imp.CallKernel
callKernelCopy bt
  destloc@(ImpGen.MemLocation destmem destshape destIxFun)
  srcloc@(ImpGen.MemLocation srcmem srcshape srcIxFun)
  n
  | Just (destoffset, srcoffset,
          num_arrays, size_x, size_y) <- isMapTranspose bt destloc srcloc =
  ImpGen.emit $ Imp.Op $ Imp.MapTranspose bt destmem destoffset srcmem srcoffset
  num_arrays size_x size_y

  | bt_size <- ImpGen.basicScalarSize bt,
    Just destoffset <-
      ImpGen.scalExpToImpExp =<<
      IxFun.linearWithOffset destIxFun bt_size,
    Just srcoffset  <-
      ImpGen.scalExpToImpExp =<<
      IxFun.linearWithOffset srcIxFun bt_size = do
        let row_size = product $ map ImpGen.dimSizeToExp $ drop 1 srcshape
        srcspace <- ImpGen.entryMemSpace <$> ImpGen.lookupMemory srcmem
        destspace <- ImpGen.entryMemSpace <$> ImpGen.lookupMemory destmem
        ImpGen.emit $ Imp.Copy
          destmem (bytes destoffset) destspace
          srcmem (bytes srcoffset) srcspace $
          (n * row_size) `Imp.withElemType` bt

  | otherwise = do
  global_thread_index <- newVName "copy_global_thread_index"

  -- Note that the shape of the destination and the source are
  -- necessarily the same.
  let shape = map ImpGen.sizeToExp destshape
      shape_se = map ImpGen.sizeToScalExp destshape
      dest_is = unflattenIndex shape_se $ ImpGen.varIndex global_thread_index
      src_is = dest_is

  makeAllMemoryGlobal $ do
    (_, destspace, destidx) <- ImpGen.fullyIndexArray' destloc dest_is bt
    (_, srcspace, srcidx) <- ImpGen.fullyIndexArray' srcloc src_is bt

    let body = Imp.Write destmem destidx bt destspace $
               Imp.Index srcmem srcidx bt srcspace

    destmem_size <- ImpGen.entryMemSize <$> ImpGen.lookupMemory destmem
    let writes_to = [Imp.MemoryUse destmem destmem_size]

    reads_from <- readsFromSet $
                  HS.singleton srcmem <>
                  freeIn destIxFun <> freeIn srcIxFun <> freeIn destshape

    kernel_size <- newVName "copy_kernel_size"
    ImpGen.emit $ Imp.DeclareScalar kernel_size Int
    ImpGen.emit $ Imp.SetScalar kernel_size $
      Imp.innerExp n * product (drop 1 shape)

    ImpGen.emit $ Imp.Op $ Imp.Kernel Imp.MapKernel {
        Imp.kernelThreadNum = global_thread_index
      , Imp.kernelSize = Imp.VarSize kernel_size
      , Imp.kernelUses = nub $ reads_from ++ writes_to
      , Imp.kernelBody = body
      }

-- | We have no bulk copy operation (e.g. memmove) inside kernels, so
-- turn any copy into a loop.
inKernelCopy :: ImpGen.CopyCompiler Imp.InKernel
inKernelCopy = ImpGen.copyElementWise

computeKernelUses :: FreeIn a =>
                     [ImpGen.ValueDestination]
                  -> a -> [VName]
                  -> ImpGen.ImpM op [Imp.KernelUse]
computeKernelUses dest kernel_body bound_in_kernel = do
    -- Find the memory blocks containing the output arrays.
    let dest_mems = mapMaybe destMem dest
        destMem (ImpGen.ArrayDestination
                 (ImpGen.CopyIntoMemory
                  (ImpGen.MemLocation mem _ _)) _) =
          Just mem
        destMem _ =
          Nothing

    -- Compute the variables that we need to pass to the kernel.
    reads_from <- readsFromSet $
                  freeIn kernel_body `HS.difference`
                  HS.fromList (dest_mems <> bound_in_kernel)

    -- Compute what memory to copy out.  Must be allocated on device
    -- before kernel execution anyway.
    writes_to <- liftM catMaybes $ forM dest $ \case
      (ImpGen.ArrayDestination
       (ImpGen.CopyIntoMemory
        (ImpGen.MemLocation mem _ _)) _) -> do
        memsize <- ImpGen.entryMemSize <$> ImpGen.lookupMemory mem
        return $ Just $ Imp.MemoryUse mem memsize
      _ ->
        return Nothing
    return $ nub $ reads_from ++ writes_to

readsFromSet :: Names -> ImpGen.ImpM op [Imp.KernelUse]
readsFromSet free =
  liftM catMaybes $
  forM (HS.toList free) $ \var -> do
    t <- lookupType var
    case t of
      Array {} -> return Nothing
      Mem _ (Space "local") -> return Nothing
      Mem memsize _ -> Just <$> (Imp.MemoryUse var <$>
                                 ImpGen.subExpToDimSize memsize)
      Basic bt ->
        if bt == Cert
        then return Nothing
        else return $ Just $ Imp.ScalarUse var bt

-- | Change every memory block to be in the global address space.
-- This is fairly hacky and can be improved once the Futhark-level
-- memory representation supports address spaces.  This only affects
-- generated code - we still need to make sure that the memory is
-- actually present on the device (and declared as variables in the
-- kernel).
makeAllMemoryGlobal :: CallKernelGen a
                    -> CallKernelGen a
makeAllMemoryGlobal =
  local $ \env -> env { ImpGen.envVtable = HM.map globalMemory $ ImpGen.envVtable env
                      , ImpGen.envDefaultSpace = Imp.Space "global"
                      }
  where globalMemory (ImpGen.MemVar entry) =
          ImpGen.MemVar entry { ImpGen.entryMemSpace = Imp.Space "global" }
        globalMemory entry =
          entry

writeThreadResult :: [VName] -> [Int] -> ImpGen.ValueDestination -> SubExp
                  -> InKernelGen ()
writeThreadResult thread_idxs perm
  (ImpGen.ArrayDestination
   (ImpGen.CopyIntoMemory
    (ImpGen.MemLocation mem dims ixfun)) _) se = do
  set <- subExpType se

  let ixfun' = IxFun.permute ixfun perm
      destloc' = ImpGen.MemLocation mem (rearrangeShape perm dims) ixfun'

  space <- ImpGen.entryMemSpace <$> ImpGen.lookupMemory mem
  let is = map ImpGen.varIndex thread_idxs
  case set of
    Basic bt -> do
      (_, _, elemOffset) <-
        ImpGen.fullyIndexArray' destloc' is bt
      ImpGen.compileResultSubExp (ImpGen.ArrayElemDestination mem bt space elemOffset) se
    _ -> do
      memloc <- ImpGen.indexArray destloc' is
      let dest = ImpGen.ArrayDestination (ImpGen.CopyIntoMemory memloc) $
                 replicate (arrayRank set) Nothing
      ImpGen.compileResultSubExp dest se
writeThreadResult _ _ _ _ =
  fail "Cannot handle kernel that does not return an array."

readKernelInput :: KernelInput ExplicitMemory
                -> InKernelGen ()
readKernelInput inp =
  when (basicType t) $ do
    (srcmem, space, srcoffset) <-
      ImpGen.fullyIndexArray arr $ map SE.intSubExpToScalExp is
    ImpGen.emit $ Imp.SetScalar name $
      Imp.Index srcmem srcoffset (elemType t) space
  where arr = kernelInputArray inp
        name = kernelInputName inp
        t = kernelInputType inp
        is = kernelInputIndices inp

isMapTranspose :: BasicType -> ImpGen.MemLocation -> ImpGen.MemLocation
               -> Maybe (Imp.Exp, Imp.Exp,
                         Imp.Exp, Imp.Exp, Imp.Exp)
isMapTranspose bt
  (ImpGen.MemLocation _ destshape destIxFun)
  (ImpGen.MemLocation _ _ srcIxFun)
  | Just (dest_offset, perm) <- IxFun.rearrangeWithOffset destIxFun bt_size,
    Just src_offset <- IxFun.linearWithOffset srcIxFun bt_size,
    permIsTranspose perm =
    isOk dest_offset src_offset
  | Just dest_offset <- IxFun.linearWithOffset destIxFun bt_size,
    Just (src_offset, perm) <- IxFun.rearrangeWithOffset srcIxFun bt_size,
    permIsTranspose perm  =
    isOk dest_offset src_offset
  | otherwise =
    Nothing
  where bt_size = ImpGen.basicScalarSize bt
        permIsTranspose = (`elem` [ [0,2,1], [1,0] ])

        isOk dest_offset src_offset = do
          dest_offset' <- ImpGen.scalExpToImpExp dest_offset
          src_offset' <- ImpGen.scalExpToImpExp src_offset
          (num_arrays, size_x, size_y) <- getSizes
          return (dest_offset', src_offset',
                  num_arrays, size_x, size_y)
        getSizes =
          case map ImpGen.sizeToExp destshape of
            [num_arrays, size_x, size_y] -> Just (num_arrays, size_x, size_y)
            [size_x, size_y]             -> Just (1, size_x, size_y)
            _                            -> Nothing

computeThreadChunkSize :: Imp.Exp
                       -> Imp.Count Imp.Elements
                       -> Imp.Count Imp.Elements
                       -> VName
                       -> ImpGen.ImpM op ()
computeThreadChunkSize thread_index elements_per_thread num_elements chunk_var = do
  starting_point <- newVName "starting_point"
  remaining_elements <- newVName "remaining_elements"

  ImpGen.emit $
    Imp.DeclareScalar starting_point Int
  ImpGen.emit $
    Imp.SetScalar starting_point $
    thread_index * Imp.innerExp elements_per_thread

  ImpGen.emit $
    Imp.DeclareScalar remaining_elements Int
  ImpGen.emit $
    Imp.SetScalar remaining_elements $
    Imp.innerExp num_elements - Imp.ScalarVar starting_point

  let no_remaining_elements = Imp.BinOp Leq (Imp.ScalarVar remaining_elements) 0
      beyond_bounds = Imp.BinOp Leq (Imp.innerExp num_elements) (Imp.ScalarVar starting_point)

  ImpGen.emit $
    Imp.If (Imp.BinOp LogOr no_remaining_elements beyond_bounds)
    (Imp.SetScalar chunk_var 0)
    (Imp.If is_last_thread
     (Imp.SetScalar chunk_var $ Imp.innerExp last_thread_elements)
     (Imp.SetScalar chunk_var $ Imp.innerExp elements_per_thread))
  where last_thread_elements =
          num_elements - Imp.elements thread_index * elements_per_thread
        is_last_thread =
          Imp.BinOp Less (Imp.innerExp num_elements) ((thread_index + 1) * Imp.innerExp elements_per_thread)
