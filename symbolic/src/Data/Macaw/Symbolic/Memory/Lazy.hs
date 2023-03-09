{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides a drop-in replacement for
-- "Data.Macaw.Symbolic.Memory". Unlike the memory model configuration in that
-- model, which populates the entire static memory in an SMT array before
-- beginning simulation, the memory model in this module lazily populates the
-- SMT array. That is, it will begin simulation without populating the SMT array
-- at all, and it instead checks before each read and write to see if a certain
-- part of the SMT array needs to be populated. This memory model also makes an
-- effort to avoid reading from the SMT array if performing concrete reads from
-- read-only sections of memory. For the full details on how this works, see
-- @Note [Lazy memory model]@.
--
-- Because the API in this module clashes with the API in
-- "Data.Macaw.Symbolic.Memory", it is recommended that you import these modules
-- with qualified imports.
module Data.Macaw.Symbolic.Memory.Lazy (
  -- * Memory Management
  memModelConfig,
  MemPtrTable,
  MSMC.toCrucibleEndian,
  MSMC.fromCrucibleEndian,
  MSMC.GlobalMemoryHooks(..),
  MSMC.defaultGlobalMemoryHooks,
  newMergedGlobalMemoryWith,
  MSMC.MemoryModelContents(..),
  mkGlobalPointerValidityPred,
  mapRegionPointers
  ) where

import           GHC.TypeLits

import qualified Control.Exception as X
import qualified Control.Lens as L
import           Control.Lens ((^.))
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.BitVector.Sized as BV
import qualified Data.Foldable as F
import qualified Data.IntervalMap.Interval as IMI
import qualified Data.IntervalMap.Strict as IM
import qualified Data.IntervalSet as IS
import qualified Data.List.Split as Split
import qualified Data.Sequence as Seq

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Vector as PV
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.MemModel.Pointer as CLP
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.Expr as WE
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Symbol as WS

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Concretize as MSC
import qualified Data.Macaw.Symbolic.Memory.Common as MSMC

-- | The configuration options for the lazy memory model:
--
-- * The supplied 'MemPtrTable' is used to translate machine words to LLVM
--   memory model pointers.
--
-- * Function calls and system calls (i.e., 'MS.lookupFunctionHandle' and
--   'MS.lookupSyscallHandle') are not supported.
--
-- * The supplied 'MemPtrTable' is used to check the validity of global
--   pointers in 'MS.mkGlobalPointerValidityAssertion'.
--
-- * Before performing a read or write, 'MS.resolvePointer' will consult an
--   online SMT solver connection in an effort to concretize the pointer being
--   read from or written to.
--
-- * 'MS.concreteImmutableGlobalRead' will use the supplied 'MemPtrTable' to
--   detect concrete reads from read-only memory, in which case the
--   'memPtrArray' will be bypassed for efficiency reasons.
--
-- * 'MS.lazilyPopulateGlobalMem' is used to incrementally populate the
--   'memPtrArray' before reads and writes.
--
-- Note some key differences between this function and the @memModelConfig@
-- function in "Data.Macaw.Symbolic.Memory":
--
-- * This function requires the personality type to be
--   'MS.MacawLazySimulatorState', as it must track which sections of global
--   memory have already been populated in the simulator state.
--
-- * This function requires an 'CBO.OnlineBackend' to make use of an online
--   SMT solver connection.
memModelConfig ::
     ( CB.IsSymBackend sym bak
     , w ~ MC.ArchAddrWidth arch
     , sym ~ WE.ExprBuilder scope st fs
     , bak ~ CBO.OnlineBackend solver scope st fs
     , WPO.OnlineSolver solver
     , MC.MemWidth w
     , 1 <= w
     , 16 <= w
     , CL.HasLLVMAnn sym
     , ?memOpts :: CL.MemOptions
     )
  => bak
  -> MemPtrTable sym w
  -> MS.MemModelConfig (MS.MacawLazySimulatorState sym w) sym arch CL.Mem
memModelConfig bak mpt =
  MS.MemModelConfig
    { MS.globalMemMap = mapRegionPointers mpt
    , MS.lookupFunctionHandle = MS.unsupportedFunctionCalls origin
    , MS.lookupSyscallHandle = MS.unsupportedSyscalls origin
    , MS.mkGlobalPointerValidityAssertion = mkGlobalPointerValidityPred mpt
    , MS.resolvePointer = MSC.resolveLLVMPtr bak
    , MS.concreteImmutableGlobalRead = concreteImmutableGlobalRead sym mpt
    , MS.lazilyPopulateGlobalMem = lazilyPopulateGlobalMemArr bak mpt
    }
  where
    sym = CB.backendGetSym bak
    origin = "the lazy macaw-symbolic memory model"

-- | An index of all of the (statically) mapped memory in a program, suitable
-- for pointer translation.
data MemPtrTable sym w = MemPtrTable
  { memPtrTable :: IM.IntervalMap (MC.MemWord w) (SymbolicMemChunk sym)
  -- ^ The ranges of (static) allocations that are mapped. Unlike the
  -- 'memPtrTable' in "Data.Macaw.Symbolic.Memory", for which the ranges of the
  -- intervals precisely correspond to the boundaries of the 'MemChunk's in the
  -- binary, this version of 'memPtrTable' has narrower intervals, each one no
  -- longer than 'chunkSize'. (See @Note [Lazy memory model]@ for an explanation
  -- of why we do this.)
  , memPtr :: CL.LLVMPtr sym w
  -- ^ The pointer to the allocation backing all of memory.
  , memPtrArray :: WI.SymArray sym (Ctx.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8)
  -- ^ The SMT array mapping addresses to symbolic bytes. Unlike the
  -- 'memPtrArray' in "Data.Macaw.Symbolic.Memory", which is fully populated
  -- before simulation begins, this version of 'memPtrArray' is incrementally
  -- populated over the course of a run of the simulator.
  , memModelContents :: MSMC.MemoryModelContents
  -- ^ How to populate bytes in writable regions of static memory in the
  -- 'memPtrArray'.
  }

-- | A discrete chunk of a memory segment within global memory. Memory is
-- lazily initialized one 'SymbolicMemChunk' at a time. See
-- @Note [Lazy memory model]@.
data SymbolicMemChunk sym = SymbolicMemChunk
  { smcBytes :: Seq.Seq (WI.SymBV sym 8)
    -- ^ A contiguous region of symbolic bytes backing global memory.
    --   The size of this region is no larger than 'chunkSize'. We represent
    --   this as a 'Seq.Seq' since we frequently need to append it to other
    --   regions (see 'combineSymbolicMemChunks').
  , smcMutability :: CL.Mutability
    -- ^ Whether the region of memory is mutable or immutable.
  }

-- | If two 'SymbolicMemChunk's have the same 'LCLM.Mutability', then return
-- @'Just' chunk@, where @chunk@ contains the two arguments' bytes concatenated
-- together. Otherwise, return 'Nothing'.
combineSymbolicMemChunks ::
  SymbolicMemChunk sym ->
  SymbolicMemChunk sym ->
  Maybe (SymbolicMemChunk sym)
combineSymbolicMemChunks
  (SymbolicMemChunk{smcBytes = bytes1, smcMutability = mutability1})
  (SymbolicMemChunk{smcBytes = bytes2, smcMutability = mutability2})
  | mutability1 == mutability2
  = Just $ SymbolicMemChunk
             { smcBytes = bytes1 <> bytes2
             , smcMutability = mutability1
             }
  | otherwise
  = Nothing

-- | @'combineIfContiguous' i1 i2@ returns 'Just' an interval with the lower
-- bound of @i1@ and the upper bound of @i2@ when one of the following criteria
-- are met:
--
-- * If @i1@ has an open upper bound, then @i2@ has a closed lower bound of the
--   same integral value.
--
-- * If @i1@ has a closed upper bound and @i2@ has an open lower bound, then
--   these bounds have the same integral value.
--
-- * If @i1@ has a closed upper bound and @i2@ has a closed lower bound, then
--   @i2@'s lower bound is equal to the integral value of @i1@'s upper bound
--   plus one.
--
-- * It is not the case that both @i1@'s upper bound and @i2@'s lower bound are
--   open.
--
-- Otherwise, this returns 'Nothing'.
--
-- Less formally, this captures the notion of combining two non-overlapping
-- 'IMI.Interval's that when would form a single, contiguous range when
-- overlaid. (Contrast this with 'IMI.combine', which only returns 'Just' if
-- the two 'IMI.Interval's are overlapping.)
combineIfContiguous :: (Eq a, Integral a) => IMI.Interval a -> IMI.Interval a -> Maybe (IMI.Interval a)
combineIfContiguous i1 i2 =
  case (i1, i2) of
    (IMI.IntervalOC lo1 hi1, IMI.IntervalOC lo2 hi2)
      | hi1 == lo2 -> Just $ IMI.IntervalOC lo1 hi2
      | otherwise  -> Nothing
    (IMI.IntervalOC lo1 hi1, IMI.OpenInterval lo2 hi2)
      | hi1 == lo2 -> Just $ IMI.OpenInterval lo1 hi2
      | otherwise  -> Nothing
    (IMI.OpenInterval lo1 hi1, IMI.IntervalCO lo2 hi2)
      | hi1 == lo2 -> Just $ IMI.OpenInterval lo1 hi2
      | otherwise  -> Nothing
    (IMI.OpenInterval lo1 hi1, IMI.ClosedInterval lo2 hi2)
      | hi1 == lo2 -> Just $ IMI.IntervalOC lo1 hi2
      | otherwise  -> Nothing
    (IMI.IntervalCO lo1 hi1, IMI.IntervalCO lo2 hi2)
      | hi1 == lo2 -> Just $ IMI.IntervalCO lo1 hi2
      | otherwise  -> Nothing
    (IMI.IntervalCO lo1 hi1, IMI.ClosedInterval lo2 hi2)
      | hi1 == lo2 -> Just $ IMI.ClosedInterval lo1 hi2
      | otherwise  -> Nothing
    (IMI.ClosedInterval lo1 hi1, IMI.IntervalOC lo2 hi2)
      | hi1 == lo2 -> Just $ IMI.ClosedInterval lo1 hi2
      | otherwise  -> Nothing
    (IMI.ClosedInterval lo1 hi1, IMI.OpenInterval lo2 hi2)
      | hi1 == lo2 -> Just $ IMI.IntervalCO lo1 hi2
      | otherwise  -> Nothing

    (IMI.IntervalOC lo1 hi1, IMI.IntervalCO lo2 hi2)
      | hi1 + 1 == lo2 -> Just $ IMI.OpenInterval lo1 hi2
      | otherwise      -> Nothing
    (IMI.IntervalOC lo1 hi1, IMI.ClosedInterval lo2 hi2)
      | hi1 + 1 == lo2 -> Just $ IMI.IntervalOC lo1 hi2
      | otherwise      -> Nothing
    (IMI.ClosedInterval lo1 hi1, IMI.IntervalCO lo2 hi2)
      | hi1 + 1 == lo2 -> Just $ IMI.IntervalCO lo1 hi2
      | otherwise      -> Nothing
    (IMI.ClosedInterval lo1 hi1, IMI.ClosedInterval lo2 hi2)
      | hi1 + 1 == lo2 -> Just $ IMI.ClosedInterval lo1 hi2
      | otherwise      -> Nothing

    (IMI.IntervalCO{}, IMI.IntervalOC{})
      -> Nothing
    (IMI.IntervalCO{}, IMI.OpenInterval{})
      -> Nothing
    (IMI.OpenInterval{}, IMI.IntervalOC{})
      -> Nothing
    (IMI.OpenInterval{}, IMI.OpenInterval{})
      -> Nothing

-- | Extend the upper bound of an 'IMI.Interval' by the given amount.
extendUpperBound :: Num a => IMI.Interval a -> a -> IMI.Interval a
extendUpperBound i extendBy =
  case i of
    IMI.IntervalCO     lo hi -> IMI.IntervalCO     lo (hi + extendBy)
    IMI.IntervalOC     lo hi -> IMI.IntervalOC     lo (hi + extendBy)
    IMI.OpenInterval   lo hi -> IMI.OpenInterval   lo (hi + extendBy)
    IMI.ClosedInterval lo hi -> IMI.ClosedInterval lo (hi + extendBy)

-- | Given a list of memory regions and the symbolic bytes backing them,
-- attempt to combine them into a single region. Return 'Just' if the memory
-- can be combined into a single, contiguous region with no overlap and the
-- backing memory has the same 'LCLM.Mutability. Return 'Nothing' otherwise.
combineChunksIfContiguous ::
  forall a sym.
  (Eq a, Integral a) =>
  [(IMI.Interval a, SymbolicMemChunk sym)] ->
  Maybe (IMI.Interval a, SymbolicMemChunk sym)
combineChunksIfContiguous ichunks =
  case L.uncons ichunks of
    Nothing -> Nothing
    Just (ichunkHead, ichunkTail) -> F.foldl' f (Just ichunkHead) ichunkTail
  where
    f ::
      Maybe (IMI.Interval a, SymbolicMemChunk sym) ->
      (IMI.Interval a, SymbolicMemChunk sym) ->
      Maybe (IMI.Interval a, SymbolicMemChunk sym)
    f acc (i2, chunk2) = do
      (i1, chunk1) <- acc
      combinedI <- combineIfContiguous i1 i2
      combinedChunk <- combineSymbolicMemChunks chunk1 chunk2
      pure (combinedI, combinedChunk)

-- | The maximum size of a 'SymbolicMemChunk', which determines the granularity
-- at which the regions of memory in a 'memPtrTable' are chunked up.
-- See @Note [Lazy memory model]@.
--
-- Currently, `chunkSize` is 1024, which is a relatively small number
-- that is the right value to be properly aligned on most architectures.
chunkSize :: Int
chunkSize = 1024

-- | @'splitInterval' x i@ returns @'Just' (i1, i2)@ if @hi - lo@ is strictly
-- greater than @x@, where:
--
-- * @lo@ is @l@'s lower bound and @hi@ is @l@'s upper bound.
--
-- * @i1@ is the subinterval of @i@ starting from @i@'s lower bound and going up
--   to (but not including) @lo + x@.
--
-- * @i2@ is the subinterval of @i@ starting from @lo + x@ and going up to @hi@.
--
-- Otherwise, this returns 'Nothing'.
--
-- This function assumes that @x@ is positive and will throw an error if this is
-- not the case.
splitInterval :: (Integral a, Ord a) => a -> IM.Interval a -> Maybe (IM.Interval a, IM.Interval a)
splitInterval x i
  | x <= 0
  = error $ "splitInterval: chunk size must be positive, got " ++ show (toInteger x)
  | x < (IMI.upperBound i - IMI.lowerBound i)
  = Just $ case i of
      IM.OpenInterval   lo hi -> (IM.OpenInterval lo (lo + x), IM.IntervalCO     (lo + x) hi)
      IM.ClosedInterval lo hi -> (IM.IntervalCO   lo (lo + x), IM.ClosedInterval (lo + x) hi)
      IM.IntervalCO     lo hi -> (IM.IntervalCO   lo (lo + x), IM.IntervalCO     (lo + x) hi)
      IM.IntervalOC     lo hi -> (IM.OpenInterval lo (lo + x), IM.ClosedInterval (lo + x) hi)
  | otherwise
  = Nothing

-- | Like the @Split.split@ function, but over an 'IM.Interval' instead of a
-- list.
chunksOfInterval :: (Integral a, Ord a) => a -> IM.Interval a -> [IM.Interval a]
chunksOfInterval x = go
  where
    go i = case splitInterval x i of
             Just (i1, i2) -> i1 : go i2
             Nothing       -> [i]

-- | @'readBytesAsRegValue' sym repr bytes@ reads symbolic bytes from @bytes@
-- and interprets it as a 'LCS.RegValue' of the appropriate type, which is
-- determined by @repr@.
--
-- This function checks that the length of @bytes@ is equal to
-- @'DMC.memReprBytes' repr@, throwing a panic if this is not the case.
readBytesAsRegValue ::
  CB.IsSymInterface sym =>
  sym ->
  MC.MemRepr ty ->
  [WI.SymBV sym 8] ->
  IO (CS.RegValue sym (MS.ToCrucibleType ty))
readBytesAsRegValue sym repr bytes =
  case repr of
    MC.BVMemRepr byteWidth endianness -> do
      bytesV <- maybe (error $ unlines
                        [ "Expected " ++ show byteWidth ++ " symbolic bytes,"
                        , "Received " ++ show (length bytes) ++ " bytes"
                        ])
                      pure
                      (PV.fromList byteWidth bytes)
      bytesBV <- readBytesAsBV sym endianness bytesV
      CL.llvmPointer_bv sym bytesBV
    MC.FloatMemRepr {} ->
      error "Reading floating point values is not currently supported"
    MC.PackedVecMemRepr {} ->
      error "Reading packed vector values is not currently supported"

-- | Read @numBytes@ worth of symbolic bytes and concatenate them into a single
-- 'WI.SymBV', respecting endianness. This is used to service concrete reads of
-- immutable global memory. See @Note [Lazy memory model]@.
readBytesAsBV
  :: forall sym numBytes
   . ( CB.IsSymInterface sym
     , 1 WI.<= numBytes
     )
  => sym
  -> MC.Endianness
  -> PV.Vector numBytes (WI.SymBV sym 8)
  -> IO (WI.SymBV sym (8 WI.* numBytes))
readBytesAsBV sym endianness = go
  where
    -- Iterate through the bytes one at a time, concatenating each byte along
    -- the way. The implementation of this function looks larger than it
    -- actually is due to needing to perform type-level Nat arithmetic to make
    -- things typecheck.
    go :: forall bytesLeft
        . (1 WI.<= bytesLeft)
       => PV.Vector bytesLeft (WI.SymBV sym 8)
       -> IO (WI.SymBV sym (8 WI.* bytesLeft))
    go bytesV =
      let resWidth = PV.length bytesV in
      let (headByte, unconsRes) = PV.uncons bytesV in
      case WI.isZeroOrGT1 (WI.decNat resWidth) of
        -- We have only one byte left, so return it.
        Left WI.Refl -> do
          WI.Refl <- return $ zeroSubEq resWidth (WI.knownNat @1)
          pure headByte
        -- We have more than one byte left, so recurse.
        Right WI.LeqProof ->
          case unconsRes of
            -- If this were Left, that would mean that there would only be
            -- one byte left, which is impossible due to the assumptions above.
            -- That is, this case is unreachable. Thankfully, GHC's constraint
            -- solver is smart enough to realize this in conjunction with
            -- EmptyCase.
            Left x -> case x of {}
            Right tailV -> do
              let recByteWidth = WI.decNat resWidth
              tailBytes <- go tailV

              WI.Refl <- return $ WI.lemmaMul (WI.knownNat @8) resWidth
              WI.Refl <- return $ WI.mulComm (WI.knownNat @8) recByteWidth
              WI.Refl <- return $ WI.mulComm (WI.knownNat @8) resWidth
              WI.LeqProof <- return $ mulMono (WI.knownNat @8) recByteWidth
              concatBytes sym endianness headByte tailBytes

-- | Concat a byte onto a larger word, respecting endianness.
concatBytes
  :: ( CB.IsSymInterface sym
     , 1 WI.<= w
     )
  => sym
  -> MC.Endianness
  -> WI.SymBV sym 8
  -> WI.SymBV sym w
  -> IO (WI.SymBV sym (8 WI.+ w))
concatBytes sym endianness byte bytes =
  case endianness of
    MC.BigEndian -> WI.bvConcat sym byte bytes
    MC.LittleEndian -> do
      WI.Refl <- return $ WI.plusComm (WI.bvWidth byte) (WI.bvWidth bytes)
      WI.bvConcat sym bytes byte

-- | Create a new LLVM memory model instance ('CL.MemImpl') and an index that
-- enables pointer translation ('MemPtrTable').
--
-- The statically-allocated memory in the 'MC.Memory' is represented by a single
-- symbolic LLVM memory model allocation, which is backed by an SMT array.
-- Unlike the @newMergedGlobalMemoryWith@ function in
-- "Data.Macaw.Symbolic.Memory", this function does /not/ populate the SMT array
-- upfront, instead deferring that task to simulation time.
-- (See @Note [Lazy memory model]@.)
newMergedGlobalMemoryWith
 :: forall arch sym bak m t st fs proxy t'
  . ( 16 <= MC.ArchAddrWidth arch
    , MC.MemWidth (MC.ArchAddrWidth arch)
    , KnownNat (MC.ArchAddrWidth arch)
    , CB.IsSymBackend sym bak
    , CL.HasLLVMAnn sym
    , MonadIO m
    , sym ~ WEB.ExprBuilder t st fs
    , ?memOpts :: CL.MemOptions
    , Traversable t'
    )
 => MSMC.GlobalMemoryHooks (MC.ArchAddrWidth arch)
 -- ^ Hooks customizing the memory setup
 -> proxy arch
 -- ^ A proxy to fix the architecture
 -> bak
 -- ^ The symbolic backend used to construct terms
 -> CLD.EndianForm
 -- ^ The endianness of values in memory
 -> MSMC.MemoryModelContents
 -- ^ A configuration option controlling how mutable memory should be represented (concrete or symbolic)
 -> t' (MC.Memory (MC.ArchAddrWidth arch))
 -- ^ The macaw memories
 -> m (CL.MemImpl sym, MemPtrTable sym (MC.ArchAddrWidth arch))
newMergedGlobalMemoryWith hooks _proxy bak endian mmc mems = do
  let sym = CB.backendGetSym bak
  let ?ptrWidth = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)

  memImpl1 <- liftIO $ CL.emptyMem endian

  let allocName = WS.safeSymbol "globalMemoryBytes"
  symArray <- liftIO $ WI.freshConstant sym allocName CT.knownRepr
  sizeBV <- liftIO $ WI.maxUnsignedBV sym ?ptrWidth
  (ptr, memImpl2) <- liftIO $ CL.doMalloc bak CL.GlobalAlloc CL.Mutable
                         "Global memory for macaw-symbolic"
                         memImpl1 sizeBV CLD.noAlignment

  tbl <- mergedMemorySymbolicMemChunks bak hooks mems
  memImpl3 <- liftIO $ CL.doArrayStore bak memImpl2 ptr CLD.noAlignment symArray sizeBV
  let ptrTable = MemPtrTable
                   { memPtrTable = tbl
                   , memPtr = ptr
                   , memPtrArray = symArray
                   , memModelContents = mmc
                   }

  return (memImpl3, ptrTable)

-- | Construct an 'IM.IntervalMap' mapping regions of memory to their bytes,
-- representing as 'SymbolicMemChunk's. The regions of memory are split apart
-- to be in units no larger than 'chunkSize' bytes.
-- See @Note [Lazy memory model]@.
mergedMemorySymbolicMemChunks ::
  forall sym bak t w m.
  ( CB.IsSymBackend sym bak
  , MC.MemWidth w
  , Traversable t
  , MonadIO m
  ) =>
  bak ->
  MSMC.GlobalMemoryHooks w ->
  t (MC.Memory w) ->
  m (IM.IntervalMap (MC.MemWord w) (SymbolicMemChunk sym))
mergedMemorySymbolicMemChunks bak hooks mems =
  fmap (IM.fromList . concat) $ traverse memorySymbolicMemChunks mems
  where
    memorySymbolicMemChunks ::
      MC.Memory w ->
      m [(IM.Interval (MC.MemWord w), SymbolicMemChunk sym)]
    memorySymbolicMemChunks mem = concat <$>
      traverse (segmentSymbolicMemChunks mem) (MC.memSegments mem)

    segmentSymbolicMemChunks ::
      MC.Memory w ->
      MC.MemSegment w ->
      m [(IM.Interval (MC.MemWord w), SymbolicMemChunk sym)]
    segmentSymbolicMemChunks mem seg = concat <$>
      traverse
        (\(addr, chunk) -> do
          allBytes <- MSMC.populateMemChunkBytes bak hooks mem seg addr chunk
          let mut | MMP.isReadonly (MC.segmentFlags seg) = CL.Immutable
                  | otherwise                            = CL.Mutable
          let absAddr =
                case MC.resolveRegionOff mem (MC.addrBase addr) (MC.addrOffset addr) of
                  Just addrOff -> MC.segmentOffset seg + MC.segoffOffset addrOff
                  Nothing -> error $
                    "segmentSymbolicMemChunks: Failed to resolve function address: " ++
                    show addr
          let size = length allBytes
          let interval = IM.IntervalCO absAddr (absAddr + fromIntegral size)
          let intervalChunks = chunksOfInterval (fromIntegral chunkSize) interval
          let smcChunks = map (\bytes -> SymbolicMemChunk
                                           { smcBytes = Seq.fromList bytes
                                           , smcMutability = mut
                                           })
                              (Split.chunksOf chunkSize allBytes)
          -- The length of these two lists should be the same, as
          -- @chunksOfInterval size@ should return a list of the same
          -- size as @Split.chunksOf size@.
          pure $ X.assert (length intervalChunks == length smcChunks)
               $ zip intervalChunks smcChunks)
        (MC.relativeSegmentContents [seg])

-- Return @Just val@ if we can be absolutely sure that this is a concrete
-- read from a contiguous region of immutable, global memory, where the type of
-- @val@ is determined by the @'MC.MemRepr' ty@ argument.
-- Return @Nothing@ otherwise. See @Note [Lazy memory model]@.
concreteImmutableGlobalRead ::
  (CB.IsSymInterface sym, MC.MemWidth w) =>
  sym ->
  MemPtrTable sym w ->
  -- ^ The global memory
  MS.ConcreteImmutableGlobalRead sym w
concreteImmutableGlobalRead sym mpt memRep ptr
  | -- First, check that the pointer being read from is concrete.
    Just ptrBlkNat <- WI.asNat ptrBlk
  , Just addrBV    <- WI.asBV ptrOff

    -- Next, check that the pointer block is the same as the block of the
    -- pointer backing global memory.
  , Just memPtrBlkNat <- WI.asNat memPtrBlk
  , ptrBlkNat == memPtrBlkNat

    -- Next, check that we are attempting to read from a contiguous region
    -- of memory.
  , let addr = fromInteger $ BV.asUnsigned addrBV
  , Just (addrBaseInterval, smc) <-
      combineChunksIfContiguous $ IM.toAscList $
      memPtrTable mpt `IM.intersecting`
        IMI.ClosedInterval addr (addr + fromIntegral numBytes)

    -- Next, check that the memory is immutable.
  , smcMutability smc == CL.Immutable

    -- Finally, check that the region of memory is large enough to cover
    -- the number of bytes we are attempting to read.
  , let addrOffset = fromIntegral $ addr - IMI.lowerBound addrBaseInterval
  , numBytes <= (length (smcBytes smc) - addrOffset)
  = do let bytes = Seq.take numBytes $
                   Seq.drop addrOffset $
                   smcBytes smc
       readVal <- readBytesAsRegValue sym memRep $ F.toList bytes
       pure $ Just readVal

  | otherwise
  = pure Nothing
  where
    numBytes = fromIntegral $ MC.memReprBytes memRep
    (ptrBlk, ptrOff) = CL.llvmPointerView ptr
    memPtrBlk = CLP.llvmPointerBlock (memPtr mpt)

-- | Prior to accessing global memory, initialize the region of memory in the
-- SMT array that backs global memory. See @Note [Lazy memory model]@.
lazilyPopulateGlobalMemArr ::
  forall sym bak w t st fs p ext.
  ( CB.IsSymBackend sym bak
  , sym ~ WEB.ExprBuilder t st fs
  , p ~ MS.MacawLazySimulatorState sym w
  , MC.MemWidth w
  ) =>
  bak ->
  MemPtrTable sym w ->
  -- ^ The global memory
  MS.LazilyPopulateGlobalMem p sym ext w
lazilyPopulateGlobalMemArr bak mpt memRep ptr state
  | -- We only wish to populate the array backing global memory if we know for
    -- sure that we are reading from the global pointer. If we're reading from a
    -- different pointer, there's no need to bother populating the array.
    WI.asNat (CLP.llvmPointerBlock (memPtr mpt)) ==
    WI.asNat (CLP.llvmPointerBlock ptr)
  = do MSMC.pleatM state tbl $ \st (addr, smc) ->
         if addr `IS.notMember` (st^.chunksL)
             && -- If dealing with a writable region of memory and the
                -- memModelContents are SymbolicMutable, then we skip populating
                -- the SMT array, instead leaving the initial contents of the
                -- memory region completely symbolic.
                not (smcMutability smc == CL.Mutable &&
                     memModelContents mpt == MSMC.SymbolicMutable)
           then do MSMC.assumeMemArr bak (memPtrArray mpt)
                     (IMI.lowerBound addr) (smcBytes smc)
                   pure $ L.over chunksL (IS.insert addr) st
           else pure st

  | otherwise
  = pure state
  where
    sym = CB.backendGetSym bak

    -- The regions of global memory that would need to be accessed as a result
    -- of reading from/writing to the pointer.  We build an interval
    -- [ptr, ptr+memRepSize] and load all of the chunks in global memory that
    -- overlap with the interval.
    tbl = IM.toAscList $ memPtrTable mpt `IM.intersecting`
                           (ptrInterval `extendUpperBound` memRepSize)
    memRepSize = fromIntegral $ MC.memReprBytes memRep

    -- ptrInterval is an interval representing the possible values that ptr
    -- could be, and memRepSize is the size of the global memory that would need
    -- to be accessed. From these we can build an interval
    -- (ptrInterval `extendUpperBound` memRepSize) that contains all possible
    -- global memory addresses that could be accessed.
    --
    -- Note that if we have a concrete read or write, then ptrInterval will be
    -- a single point in the address space. The only way that this interval can
    -- span multiple addresses is if we have a symbolic read or write.
    ptrInterval = symBVInterval sym (CLP.llvmPointerOffset ptr)

    chunksL :: forall rtp f args.
               L.Lens' (CS.SimState p sym ext rtp f args)
                       (IS.IntervalSet (IMI.Interval (MC.MemWord w)))
    chunksL = CS.stateContext . CS.cruciblePersonality . MS.populatedMemChunks

-- | Return an 'IMI.Interval' representing the possible range of addresses that
-- a 'WI.SymBV' can lie between. If this is a concrete bitvector, the interval
-- will consist of a single point, but if this is a symbolic bitvector, then
-- the range can span multiple addresses.
symBVInterval ::
  (WI.IsExprBuilder sym, MC.MemWidth w) =>
  sym ->
  WI.SymBV sym w ->
  IMI.Interval (MC.MemWord w)
symBVInterval _ bv =
  case WI.unsignedBVBounds bv of
    Just (lo, hi) -> IMI.ClosedInterval (fromInteger lo) (fromInteger hi)
    Nothing       -> IMI.ClosedInterval minBound maxBound

-- | Create a function that computes a validity predicate for an LLVMPointer
-- that may point to the static global memory region.
--
-- We represent all of the statically allocated storage in a binary in a single
-- LLVM array.  This array is sparse, meaning that large ranges of the address
-- space are not actually mapped.  Whenever we use a pointer into this memory
-- region, we want to assert that it is inside one of the mapped regions and
-- that it does not violate any mutability constraints.
--
-- The mapped regions are recorded in the MemPtrTable.
--
-- We need to be a little careful: if the BlockID of the pointer is definitely
-- zero, we make a direct assertion.  Otherwise, if the pointer is symbolic, we
-- have to conditionally assert the range validity.
--
-- Note that we pass in an indication of the use of the pointer: if the pointer
-- is used to write, it must only be within the writable portion of the address
-- space (which is also recorded in the MemPtrTable).  If the write is
-- conditional, we must additionally mix in the predicate.
--
-- This is intended as a reasonable implementation of the
-- 'MS.MkGlobalPointerValidityPred'.
mkGlobalPointerValidityPred ::
     forall sym w
   . ( CB.IsSymInterface sym
     , MC.MemWidth w
     )
  => MemPtrTable sym w
  -> MS.MkGlobalPointerValidityAssertion sym w
mkGlobalPointerValidityPred mpt =
  MSMC.mkGlobalPointerValidityPredCommon $ fmap smcMutability $ memPtrTable mpt

-- | Construct a translator for machine addresses into LLVM memory model pointers.
--
-- This translator is used by the symbolic simulator to resolve memory addresses.
mapRegionPointers :: ( MC.MemWidth w
                         , 16 <= w
                         , CB.IsSymInterface sym
                         , CL.HasLLVMAnn sym
                         , ?memOpts :: CL.MemOptions
                         )
                      => MemPtrTable sym w
                      -> MS.GlobalMap sym CL.Mem w
mapRegionPointers mpt =
  MSMC.mapRegionPointersCommon (memPtr mpt)

-- Additional proof combinators

mulMono :: forall p q x w. (1 WI.<= x, 1 WI.<= w) => p x -> q w -> WI.LeqProof 1 (x WI.* w)
mulMono x w = WI.leqTrans (WI.LeqProof @1 @w) (WI.leqMulMono x w)

zeroSubEq :: forall p q w n. (n WI.<= w, 0 ~ (w WI.- n)) => p w -> q n -> w WI.:~: n
zeroSubEq w n
  | WI.Refl <- WI.minusPlusCancel w n
  = WI.Refl

{-
Note [Lazy memory model]
~~~~~~~~~~~~~~~~~~~~~~~~
macaw-symbolic's default memory model backs the global memory in a binary with
an SMT array of symbolic bytes. One issue with this approach is that
initializing the elements of this array is expensive. Despite our best efforts
to optimize how SMT array initialization takes places (see `assumeMemArr`),
filling in each byte of a large (i.e., several megabytes or more) binary
upfront is usually enough eat up all the RAM on your machine. While it is not
immediately obvious what causes this, some related work on the subject of SMT
array performance can be found in these issues:

* https://github.com/Z3Prover/z3/issues/1150
* https://github.com/Z3Prover/z3/issues/5129

For this reason, we also offer an alternative, lazy memory model that
deliberately avoid populating the entire array upfront. Instead, this
initializes memory lazily. Here is a first approximation of how this works:

* When the simulation starts, we create an empty SMT array to back global
  memory but do not initialize any of its elements. (See
  `newMergedGlobalMemoryWith` for how this is implemented.) We store this array
  in a `MemPtrTable` for later use.

* At the same time, we also store an IntervalMap in the MemPtrTable
  that maps the addresses in each memory segment to the corresponding bytes.
  (See the `SymbolicMemChunk` data type, which stores these bytes.)

  We also store an IntervalSet in a MacawLazySimulatorState that tracks which
  regions of memory we have encountered thus far. (See `populatedMemChunks`.)
  This will be empty before the start of simulation.

* During simulation, if we attempt to access global memory, we first check
  to see if we have previously accessed the memory segment(s) corresponding to
  the addresses that were are accessing. If we haven't, we then initialize the
  bytes corresponding to those memory segments (and _only_ those memory
  segments) in the SMT array. We then record the fact that we have accessed
  these segments in the `populatedMemChunks` field of the
  `MacawLazySimulatorState`.

* How do we determine which memory segments correspond to a particular read or
  write? If it is a concrete read or write, this is straightforward, as we need
  only look up a single address in the IntervalMap. If it is a symbolic read or
  write, then things are trickier, since it could potentially access different
  memory regions. To accommodate this, we construct an interval spanning all of
  the possible addresses that the read/write could access (see `ptrInterval` in
  `lazilyPopulateGlobalMemArr`) and retrieve all parts of the IntervalMap that
  intersect with the interval. This is costly when dealing with symbolic reads
  and writes, but it ensures that the approach is sound.

This approach ensures that we only pay the cost of memory initialization when
it is absolutely necessary. In order to make it less costly, we also implement
two important optimizations:

1. Even if the memory is only initialized one memory segment at a time, that
   can still be expensive if one accesses memory in a very large segment.
   What's more, one usually only needs to access a small portion of the
   large segment, but with the approach described above, you'd still have to pay
   the cost of initializing the entire segment.

   For this reason, we split up the memory addresses at an even finer
   granularity than just the memory segments when creating the IntervalMap.
   We go further and split up each segment into chunks of `chunkSize` bytes
   each. This way, most memory accesses will only require initializing small
   chunks of the array, even if they happen to reside within large memory
   segments.

   Currently, `chunkSize` is 1024, which is a relatively small number
   that is the right value to be properly aligned on most architectures.

2. While tracking the writable global memory in an SMT array is important in
   case the memory gets updated, there's really no need to track the
   read-only global memory in an SMT array. After all, read-only memory can
   never be updated, so we can determine what read-only memory will be by
   looking up the corresponding bytes in the IntervalMap, bypassing the SMT
   array completely.

   To determine which parts of memory are read-only, each `SymbolicMemChunk`
   tracks whether its bytes are mutable or immutable. When performing a memory
   read, if we can conclude that all of the memory to be read is immutable
   (i.e., read-only), then we can convert the symbolic bytes to a bitvector.
   (See `readBytesAsRegValue` for how this is implemented.)

   There are several criteria that must be met in order for this to be
   possible:

   * The read must be concrete.

   * The amount of bytes to be read must lie within a contiguous part of
     read-only memory.

   * There must be enough bytes within this part of memory to cover the number
     of bytes that must be read.

   If one of these critera are not met, we fall back on the SMT array approach.

Fundamentally, the lazy memory model sacrifices more space (in the form of
having to track each byte of the global address space in the `memPtrTable`) in
exchange for fewer SMT array accesses at simulation time, which generally
results in better performance as binary sizes increase. If SMT solvers improve
their performance with respect to arrays in the future, however, it is possible
that the default memory model could be a better choice. For this reason, we
provide both memory models as options.
-}
