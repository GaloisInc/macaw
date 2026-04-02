{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Internal module for "Data.Macaw.Symbolic.Memory.Lazy".
--
-- This module exposes all internals for testing purposes.
-- Mainly, we want to test 'concreteUnmutatedGlobalRead'.
--
-- The public API is re-exported by "Data.Macaw.Symbolic.Memory.Lazy".
module Data.Macaw.Symbolic.Memory.Lazy.Internal (
  -- * Public API
  memModelConfig,
  MemPtrTable(..),
  newGlobalMemory,
  newGlobalMemoryWith,
  newMergedGlobalMemoryWith,
  mkGlobalPointerValidityPred,
  mapRegionPointers,

  -- * Internal (exported for testing)
  SymbolicMemChunk(..),
  symChunkLen,
  checkContiguous,
  extendUpperBound,
  splitInterval,
  chunksOfInterval,
  chunkSize,
  readBytesAsRegValue,
  readBytesAsBV,
  concatBytes,
  mergedMemorySymbolicMemChunks,
  concreteUnmutatedGlobalRead,
  concreteUnmutatedGlobalReadWithPopulatedChunks,
  lazilyPopulateGlobalMemArr,
  symBVInterval,
  mulMono,
  zeroSubEq,
  -- ** ByteCache re-exports
  MBC.ByteCache,
  MBC.mkByteCache,
  MBC.indexByteCache,
  MBC.indexByteCacheM
  ) where

import           GHC.TypeLits

import qualified Control.Exception as X
import qualified Control.Lens as L
import           Control.Lens ((^.))
import           Control.Monad ( guard )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.List as List
import           Data.Functor.Identity ( Identity(Identity) )
import qualified Data.IntervalMap.Interval as IMI
import qualified Data.IntervalMap.Strict as IM
import qualified Data.IntervalSet as IS
import qualified Data.Vector as Vec

import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Vector as PV
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Macaw.Symbolic.Memory.ByteCache as MBC
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Backend.ProofGoals as CBP
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
-- * 'MS.concreteUnmutatedGlobalRead' will use the supplied 'MemPtrTable' to
--   detect concrete reads from unmutated memory, in which case the
--   'memPtrArray' will be bypassed for efficiency reasons.
--
-- * 'MS.lazilyPopulateGlobalMem' is used to incrementally populate the
--   'memPtrArray' before reads and writes.
--
-- Note some key differences between this function and the @memModelConfig@
-- function in "Data.Macaw.Symbolic.Memory":
--
-- * This function requires the personality type to be an instance of
--   'MS.HasMacawLazySimulatorState', as it must track which sections of global
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
     , MS.HasMacawLazySimulatorState p sym w
     , MC.MemWidth w
     , 1 <= w
     , 16 <= w
     , CL.HasLLVMAnn sym
     , ?memOpts :: CL.MemOptions
     , MSMC.MacawProcessAssertion sym
     )
  => bak
  -> MemPtrTable sym w
  -> MS.MemModelConfig p sym arch CL.Mem
memModelConfig bak mpt =
  MS.MemModelConfig
    { MS.globalMemMap = mapRegionPointers mpt
    , MS.lookupFunctionHandle = MS.unsupportedFunctionCalls origin
    , MS.lookupSyscallHandle = MS.unsupportedSyscalls origin
    , MS.mkGlobalPointerValidityAssertion = mkGlobalPointerValidityPred mpt
    , MS.resolvePointer = MSC.resolveLLVMPtr bak
    , MS.concreteUnmutatedGlobalRead =
        concreteUnmutatedGlobalRead
          sym
          (memMutableTable mpt)
          (memImmutableTable mpt)
          (byteCache mpt)
          (CLP.llvmPointerBlock (memPtr mpt))
          (memModelContents mpt)
    , MS.lazilyPopulateGlobalMem = lazilyPopulateGlobalMemArr bak mpt
    }
  where
    sym = CB.backendGetSym bak
    origin = "the lazy macaw-symbolic memory model"

-- | An index of all of the (statically) mapped memory in a program, suitable
-- for pointer translation.
data MemPtrTable sym w = MemPtrTable
  { memMutableTable :: MSMC.MutableIntervalMap (MC.MemWord w) (SymbolicMemChunk sym)
  -- ^ Mutable memory regions, chunked into intervals of at most 'chunkSize'
  -- bytes for fine-grained lazy population.
  -- See @Note [Lazy memory model]@.
  , memImmutableTable :: MSMC.ImmutableIntervalMap (MC.MemWord w) (SymbolicMemChunk sym)
  -- ^ Immutable (read-only) memory regions, also chunked to 'chunkSize'.
  -- Used directly by 'concreteUnmutatedGlobalRead' for concrete reads, and
  -- lazily populated into the SMT array for symbolic reads.
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
  , byteCache :: MBC.ByteCache sym
  -- ^ See "Data.Macaw.Symbolic.Memory.ByteCache"
  }

-- | A discrete chunk of a memory segment within global memory. Memory is
-- lazily initialized one 'SymbolicMemChunk' at a time. See
-- @Note [Lazy memory model]@.
--
-- For the common case of concrete byte data from the binary, we store the raw
-- 'BS.ByteString' to avoid materializing What4 expressions upfront. Expressions
-- are only created on demand when a chunk is actually accessed, using the
-- shared 'MBC.ByteCache'.
data SymbolicMemChunk sym
  = ConcreteBytes !BS.ByteString
    -- ^ Raw bytes from the binary (e.g., from 'MC.ByteRegion'). Symbolic
    --   expressions are created on demand during lazy population via the
    --   shared 'MBC.ByteCache'.
  | SymbolicBytes !(Vec.Vector (WI.SymBV sym 8))
    -- ^ Truly symbolic bytes (e.g., from relocations) that cannot be
    --   represented as a raw 'BS.ByteString'.

-- | The number of bytes in a 'SymbolicMemChunk'.
symChunkLen :: SymbolicMemChunk sym -> Int
symChunkLen = \case
  ConcreteBytes bs -> BS.length bs
  SymbolicBytes s  -> Vec.length s

-- | Split a 'BS.ByteString' into chunks of at most @n@ bytes.
bsChunksOf :: Int -> BS.ByteString -> [BS.ByteString]
bsChunksOf n bs
  | BS.null bs = []
  | otherwise  = let (h, t) = BS.splitAt n bs in h : bsChunksOf n t

-- | Split a 'Vec.Vector' into chunks of at most @n@ elements.
vecChunksOf :: Int -> Vec.Vector a -> [Vec.Vector a]
vecChunksOf n v
  | Vec.null v = []
  | otherwise  = let (h, t) = Vec.splitAt n v in h : vecChunksOf n t

-- | @'checkContiguous' i1 i2@ returns 'True' when one of the following
-- criteria are met:
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
-- Otherwise, this returns 'False'.
--
-- Less formally, this captures the notion of checking whether two
-- non-overlapping 'IMI.Interval's would form a single, contiguous range when
-- overlaid. (Contrast this with 'IMI.combine', which only returns 'Just' if
-- the two 'IMI.Interval's are overlapping.)
checkContiguous :: (Eq a, Integral a) => IMI.Interval a -> IMI.Interval a -> Bool
checkContiguous i1 i2 =
  case (i1, i2) of
    (IMI.IntervalOC _ hi1, IMI.IntervalOC lo2 _)
      | hi1 == lo2 -> True
      | otherwise  -> False
    (IMI.IntervalOC _ hi1, IMI.OpenInterval lo2 _)
      | hi1 == lo2 -> True
      | otherwise  -> False
    (IMI.OpenInterval _ hi1, IMI.IntervalCO lo2 _)
      | hi1 == lo2 -> True
      | otherwise  -> False
    (IMI.OpenInterval _ hi1, IMI.ClosedInterval lo2 _)
      | hi1 == lo2 -> True
      | otherwise  -> False
    (IMI.IntervalCO _ hi1, IMI.IntervalCO lo2 _)
      | hi1 == lo2 -> True
      | otherwise  -> False
    (IMI.IntervalCO _ hi1, IMI.ClosedInterval lo2 _)
      | hi1 == lo2 -> True
      | otherwise  -> False
    (IMI.ClosedInterval _ hi1, IMI.IntervalOC lo2 _)
      | hi1 == lo2 -> True
      | otherwise  -> False
    (IMI.ClosedInterval _ hi1, IMI.OpenInterval lo2 _)
      | hi1 == lo2 -> True
      | otherwise  -> False

    (IMI.IntervalOC _ hi1, IMI.IntervalCO lo2 _)
      | hi1 + 1 == lo2 -> True
      | otherwise      -> False
    (IMI.IntervalOC _ hi1, IMI.ClosedInterval lo2 _)
      | hi1 + 1 == lo2 -> True
      | otherwise      -> False
    (IMI.ClosedInterval _ hi1, IMI.IntervalCO lo2 _)
      | hi1 + 1 == lo2 -> True
      | otherwise      -> False
    (IMI.ClosedInterval _ hi1, IMI.ClosedInterval lo2 _)
      | hi1 + 1 == lo2 -> True
      | otherwise      -> False

    (IMI.IntervalCO{}, IMI.IntervalOC{})
      -> False
    (IMI.IntervalCO{}, IMI.OpenInterval{})
      -> False
    (IMI.OpenInterval{}, IMI.IntervalOC{})
      -> False
    (IMI.OpenInterval{}, IMI.OpenInterval{})
      -> False

-- | Extend the upper bound of an 'IMI.Interval' by the given amount.
extendUpperBound :: Num a => IMI.Interval a -> a -> IMI.Interval a
extendUpperBound i extendBy =
  case i of
    IMI.IntervalCO     lo hi -> IMI.IntervalCO     lo (hi + extendBy)
    IMI.IntervalOC     lo hi -> IMI.IntervalOC     lo (hi + extendBy)
    IMI.OpenInterval   lo hi -> IMI.OpenInterval   lo (hi + extendBy)
    IMI.ClosedInterval lo hi -> IMI.ClosedInterval lo (hi + extendBy)

-- | Given a read address, a number of bytes, and a list of memory regions with
-- backing bytes, extract the requested bytes by slicing the chunks.
--
-- @
--      chunk0         chunk1     chunk2       chunk3
--  |--------------|------------|--------|---------------|
--  |skip|         |                     |tail|
--       |<------------ numBytes ------------>|
--      addr                             addr + numBytes
-- @
--
-- Returns 'Just' if the chunks are contiguous, immutable or mutable but
-- unpopulated, and cover the full read window. Returns 'Nothing' otherwise.
-- Chunks are valid if they are immutable OR mutable but unpopulated.
sliceContiguousChunks ::
  forall a sym.
  (Eq a, Integral a) =>
  MBC.ByteCache sym ->
  a ->
  -- ^ The address being read from
  Int ->
  -- ^ Number of bytes to read
  [(IMI.Interval a, SymbolicMemChunk sym)] ->
  -- ^ Mutable chunks
  [(IMI.Interval a, SymbolicMemChunk sym)] ->
  -- ^ Immutable chunks
  MSMC.MemoryModelContents ->
  -- ^ How mutable memory is modeled
  IS.IntervalSet (IMI.Interval a) ->
  -- ^ Populated chunks (we cannot use mutable chunks in this set)
  Maybe [WI.SymBV sym 8]
sliceContiguousChunks cache addr numBytes mutChunks immutChunks memContents populatedChunks
    | numBytes <= 0 = Just []
    | otherwise = do
        (firstI, firstC, muts', immuts') <- popNext mutChunks immutChunks
        guard (addr >= IMI.lowerBound firstI)
        let skip = convert (addr - IMI.lowerBound firstI)
            firstLen = intervalLen firstI
            avail = firstLen - skip
            firstTake = min numBytes avail
            trimmedFirst = sliceBytes skip firstTake firstC
        X.assert (firstTake > 0) $ guard (firstTake > 0)
        let remaining = numBytes - firstTake
        go firstI remaining trimmedFirst muts' immuts'
  where
    convert = fromIntegral @a @Int

    -- Pop the next valid interval from whichever list has the smaller lower
    -- bound.
    popNext ::
      [(IMI.Interval a, SymbolicMemChunk sym)] ->
      [(IMI.Interval a, SymbolicMemChunk sym)] ->
      Maybe (IMI.Interval a, SymbolicMemChunk sym,
             [(IMI.Interval a, SymbolicMemChunk sym)],
             [(IMI.Interval a, SymbolicMemChunk sym)])
    popNext = \cases
      [] [] -> Nothing
      ((i, c) : ms) [] -> do
        validMutable i
        Just (i, c, ms, [])
      [] ((i, c) : is) -> Just (i, c, [], is)
      ms@((mi, mc) : ms') is@((ii, ic) : is')
        | IMI.lowerBound mi <= IMI.lowerBound ii -> do
            validMutable mi
            Just (mi, mc, ms', is)
        | otherwise -> Just (ii, ic, ms, is')
      where
        validMutable i =
          guard (memContents /= MSMC.SymbolicMutable
              && i `IS.notMember` populatedChunks)

    -- We expect IntervalCOs
    intervalLen :: IMI.Interval a -> Int
    intervalLen = \case
      IMI.IntervalCO lo hi -> convert (hi - lo)
      _ -> X.assert False 0

    sliceBytes :: Int -> Int -> SymbolicMemChunk sym -> [WI.SymBV sym 8]
    sliceBytes drop_ take_ = \case
      ConcreteBytes bs ->
        [ MBC.indexByteCache cache (BS.index bs i)
        | i <- [drop_ .. drop_ + take_ - 1]
        ]
      SymbolicBytes s ->
        Vec.toList (Vec.slice drop_ take_ s)

    takeBytes :: Int -> SymbolicMemChunk sym -> [WI.SymBV sym 8]
    takeBytes = sliceBytes 0

    allBytes :: SymbolicMemChunk sym -> [WI.SymBV sym 8]
    allBytes mcb = sliceBytes 0 (symChunkLen mcb) mcb

    go ::
      IMI.Interval a -> Int -> [WI.SymBV sym 8] ->
      [(IMI.Interval a, SymbolicMemChunk sym)] ->
      [(IMI.Interval a, SymbolicMemChunk sym)] ->
      Maybe [WI.SymBV sym 8]
    go prev remaining acc muts immuts
      | remaining <= 0 = X.assert (length acc == numBytes) $ Just acc
      | otherwise = do
          (ival, chunk, muts', immuts') <- popNext muts immuts
          guard (checkContiguous prev ival)
          let chunkLen = intervalLen ival
          let remaining' = remaining - chunkLen
          -- (++) is O(n^2), but these lists are a maximum of 8 elements (bytes)
          if remaining' < 0
            then let result = acc ++ takeBytes remaining chunk
                 in X.assert (length result == numBytes) $ Just result
            else go ival remaining'
                    (acc ++ allBytes chunk) muts' immuts'

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
newGlobalMemory :: ( 16 <= MC.ArchAddrWidth arch
                   , MC.MemWidth (MC.ArchAddrWidth arch)
                   , KnownNat (MC.ArchAddrWidth arch)
                   , CB.IsSymBackend sym bak
                   , CL.HasLLVMAnn sym
                   , MonadIO m
                   , sym ~ WEB.ExprBuilder t st fs
                   , ?memOpts :: CL.MemOptions
                   )
                => proxy arch
                -- ^ A proxy to fix the architecture
                -> bak
                -- ^ The symbolic backend used to construct terms
                -> CLD.EndianForm
                -- ^ The endianness of values in memory
                -> MSMC.MemoryModelContents
                -- ^ A configuration option controlling how mutable memory should be represented (concrete or symbolic)
                -> MC.Memory (MC.ArchAddrWidth arch)
                -- ^ The macaw memory
                -> m (CL.MemImpl sym, MemPtrTable sym (MC.ArchAddrWidth arch))
newGlobalMemory = newGlobalMemoryWith MSMC.defaultGlobalMemoryHooks

-- | A version of 'newGlobalMemory' that enables some of the memory model
-- initialization to be configured via 'GlobalMemoryHooks'.
--
-- This version enables callers to control behaviors for which there is no good
-- default behavior (and that must be otherwise treated as an error).
newGlobalMemoryWith
 :: ( 16 <= MC.ArchAddrWidth arch
    , MC.MemWidth (MC.ArchAddrWidth arch)
    , KnownNat (MC.ArchAddrWidth arch)
    , CB.IsSymBackend sym bak
    , CL.HasLLVMAnn sym
    , MonadIO m
    , sym ~ WEB.ExprBuilder t st fs
    , ?memOpts :: CL.MemOptions
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
 -> MC.Memory (MC.ArchAddrWidth arch)
 -- ^ The macaw memory
 -> m (CL.MemImpl sym, MemPtrTable sym (MC.ArchAddrWidth arch))
newGlobalMemoryWith hooks proxy bak endian mmc mem =
  newMergedGlobalMemoryWith hooks proxy bak endian mmc (Identity mem)

-- | A version of 'newGlobalMemoryWith' that takes a 'Foldable' collection of
-- memories and merges them into a flat addresses space.  The address spaces of
-- the input memories must not overlap.
--
-- In the future this function may be updated to support multiple merge
-- strategies by adding additional configuration options to
-- 'GlobalMemoryHooks'.
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

  (mutTbl, immutTbl) <- mergedMemorySymbolicMemChunks bak hooks mems

  -- Create the shared byte cache once (all 256 possible byte values)
  cache <- liftIO $ MBC.mkByteCache sym

  memImpl3 <- liftIO $ CL.doArrayStore bak memImpl2 ptr CLD.noAlignment symArray sizeBV
  let ptrTable = MemPtrTable
                   { memMutableTable = mutTbl
                   , memImmutableTable = immutTbl
                   , memPtr = ptr
                   , memPtrArray = symArray
                   , memModelContents = mmc
                   , byteCache = cache
                   }

  return (memImpl3, ptrTable)

-- | Construct two 'IM.IntervalMap's mapping regions of memory to their bytes,
-- representing as 'SymbolicMemChunk's. Returns @(mutableMap, immutableMap)@.
-- Both maps have intervals split into units no larger than 'chunkSize' bytes.
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
  m ( MSMC.MutableIntervalMap (MC.MemWord w) (SymbolicMemChunk sym)
    , MSMC.ImmutableIntervalMap (MC.MemWord w) (SymbolicMemChunk sym)
    )
mergedMemorySymbolicMemChunks bak hooks mems = do
  pairs <- traverse memorySymbolicMemChunks mems
  let (muts, immuts) = foldMap id pairs
  pure ( MSMC.MutableIntervalMap (IM.fromList muts)
       , MSMC.ImmutableIntervalMap (IM.fromList immuts)
       )
  where
    memorySymbolicMemChunks ::
      MC.Memory w ->
      m ( [(IM.Interval (MC.MemWord w), SymbolicMemChunk sym)]
        , [(IM.Interval (MC.MemWord w), SymbolicMemChunk sym)]
        )
    memorySymbolicMemChunks mem = do
      pairs <- traverse (segmentSymbolicMemChunks mem) (MC.memSegments mem)
      pure (foldMap id pairs)

    segmentSymbolicMemChunks ::
      MC.Memory w ->
      MC.MemSegment w ->
      m ( [(IM.Interval (MC.MemWord w), SymbolicMemChunk sym)]
        , [(IM.Interval (MC.MemWord w), SymbolicMemChunk sym)]
        )
    segmentSymbolicMemChunks mem seg = do
      pairs <- traverse
        (\(addr, chunk) -> do
          let mut | MMP.isReadonly (MC.segmentFlags seg) = CL.Immutable
                  | otherwise                            = CL.Mutable
          let absAddr =
                case MC.resolveRegionOff mem (MC.addrBase addr) (MC.addrOffset addr) of
                  Just addrOff -> MC.segmentOffset seg + MC.segoffOffset addrOff
                  Nothing -> error $
                    "segmentSymbolicMemChunks: Failed to resolve function address: " ++
                    show addr
          (smcChunks, size) <- memChunkToSymbolic mem seg addr chunk
          let interval = IM.IntervalCO absAddr (absAddr + fromIntegral size)
          let intervalChunks = chunksOfInterval (fromIntegral chunkSize) interval
          -- The length of these two lists should be the same, as
          -- @chunksOfInterval size@ should return a list of the same
          -- size as @bsChunksOf size@ or @vecChuknsOf size@.
          let ichunks = X.assert (length intervalChunks == length smcChunks)
                      $ zip intervalChunks smcChunks
          case mut of
            CL.Mutable   -> pure (ichunks, [])
            CL.Immutable -> pure ([], ichunks)
        )
        (MC.relativeSegmentContents [seg])
      pure (foldMap id pairs)

    memChunkToSymbolic ::
      MC.Memory w ->
      MC.MemSegment w ->
      MC.MemAddr w ->
      MC.MemChunk w ->
      m ([SymbolicMemChunk sym], Int)
    memChunkToSymbolic mem seg addr = \case
      MC.ByteRegion bs ->
        pure (concreteChunks bs, BS.length bs)
      MC.BSSRegion sz ->
        let szInt = fromIntegral @(MC.MemWord w) @Int sz
            bs = BS.replicate szInt 0
        in pure (concreteChunks bs, szInt)
      MC.RelocationRegion reloc -> do
        symBytes <- liftIO $
          MSMC.populateRelocation hooks bak mem seg addr reloc
        let len = length symBytes
        pure (symbolicChunks (Vec.fromList symBytes), len)
      where
        concreteChunks :: BS.ByteString -> [SymbolicMemChunk sym]
        concreteChunks bs = map ConcreteBytes (bsChunksOf chunkSize bs)

        symbolicChunks :: Vec.Vector (WI.SymBV sym 8) -> [SymbolicMemChunk sym]
        symbolicChunks v = map SymbolicBytes (vecChunksOf chunkSize v)


-- Return @Just val@ if we can be absolutely sure that this is a concrete
-- read from a contiguous region of unmutated global memory, where the type of
-- @val@ is determined by the @'MC.MemRepr' ty@ argument.
-- Return @Nothing@ otherwise. See @Note [Lazy memory model]@.
concreteUnmutatedGlobalRead ::
  forall sym w p.
  ( CB.IsSymInterface sym
  , MC.MemWidth w
  , MS.HasMacawLazySimulatorState p sym w
  ) =>
  sym ->
  MSMC.MutableIntervalMap (MC.MemWord w) (SymbolicMemChunk sym) ->
  MSMC.ImmutableIntervalMap (MC.MemWord w) (SymbolicMemChunk sym) ->
  MBC.ByteCache sym ->
  -- ^ Byte cache for creating symbolic expressions on demand
  WI.SymNat sym ->
  -- ^ The global memory block number
  MSMC.MemoryModelContents ->
  -- ^ How mutable memory is modeled
  MS.ConcreteUnmutatedGlobalRead p sym w
concreteUnmutatedGlobalRead sym mutMap immutMap cache memPtrBlk memContents personality =
  let popChunks = personality ^. MS.populatedMemChunks in
  concreteUnmutatedGlobalReadWithPopulatedChunks sym mutMap immutMap cache memPtrBlk memContents popChunks

concreteUnmutatedGlobalReadWithPopulatedChunks ::
  forall sym w ty.
  ( CB.IsSymInterface sym
  , MC.MemWidth w
  ) =>
  sym ->
  MSMC.MutableIntervalMap (MC.MemWord w) (SymbolicMemChunk sym) ->
  MSMC.ImmutableIntervalMap (MC.MemWord w) (SymbolicMemChunk sym) ->
  MBC.ByteCache sym ->
  WI.SymNat sym ->
  MSMC.MemoryModelContents ->
  IS.IntervalSet (IMI.Interval (MC.MemWord w)) ->
  MC.MemRepr ty ->
  CL.LLVMPtr sym w ->
  IO (Maybe (CS.RegValue sym (MS.ToCrucibleType ty)))
concreteUnmutatedGlobalReadWithPopulatedChunks sym mm im cache memPtrBlk memContents populatedChunks memRep ptr
  | let MSMC.MutableIntervalMap mutMap = mm
  , let MSMC.ImmutableIntervalMap immutMap = im

    -- First, check that the pointer being read from is concrete.
  , Just ptrBlkNat <- WI.asNat ptrBlk
  , Just addrBV    <- WI.asBV ptrOff

    -- Next, check that the pointer block is the same as the block of the
    -- pointer backing global memory.
  , Just memPtrBlkNat <- WI.asNat memPtrBlk
  , ptrBlkNat == memPtrBlkNat

    -- Next, look up the chunks that intersect the read range and try to extract
    -- contiguous, unmutated bytes covering the full read.
  , let addr = fromInteger @(MC.MemWord w) $ BV.asUnsigned addrBV
  , let endAddr = addr + fromIntegral @Int @(MC.MemWord w) numBytes
  , let mutChunks = IM.toAscList $
          mutMap `IM.intersecting` IMI.IntervalCO addr endAddr
  , let immutChunks = IM.toAscList $
          immutMap `IM.intersecting` IMI.IntervalCO addr endAddr
  , Just bytes <- sliceContiguousChunks cache addr numBytes mutChunks immutChunks memContents populatedChunks
  = do readVal <- readBytesAsRegValue sym memRep bytes
       pure $ Just readVal

  | otherwise
  = pure Nothing
  where
    numBytes = fromIntegral $ MC.memReprBytes memRep
    (ptrBlk, ptrOff) = CL.llvmPointerView ptr

-- | Prior to accessing global memory, initialize the region of memory in the
-- SMT array that backs global memory. See @Note [Lazy memory model]@.
lazilyPopulateGlobalMemArr ::
  forall sym bak w t st fs p ext.
  ( CB.IsSymBackend sym bak
  , sym ~ WEB.ExprBuilder t st fs
  , MS.HasMacawLazySimulatorState p sym w
  , MC.MemWidth w
  ) =>
  bak ->
  MemPtrTable sym w ->
  -- ^ The global memory
  MS.LazilyPopulateGlobalMem p sym ext w
lazilyPopulateGlobalMemArr bak mpt useTag memRep ptr state
  | -- We only wish to populate the array backing global memory if we know for
    -- sure that we are reading from the global pointer. If we're reading from a
    -- different pointer, there's no need to bother populating the array.
    WI.asNat (CLP.llvmPointerBlock (memPtr mpt)) ==
    WI.asNat (CLP.llvmPointerBlock ptr)
  = do -- Build the interval of global memory addresses that could be accessed.
       -- If the pointer is concrete, this is a single point; if symbolic, it
       -- can span multiple addresses.
       let accessInterval =
             symBVInterval sym (CLP.llvmPointerOffset ptr)
               `extendUpperBound` fromIntegral (MC.memReprBytes memRep)
           ivals tbl =
             IM.toAscList $ tbl `IM.intersecting` accessInterval

       -- Collect assumptions for all unpopulated chunks, then add them
       -- in a single restoreAssumptionState call.
       -- See @Note [Top-level assumptions]@.
       let populated = state ^. chunksL
           collectChunk (as, addrs) (addr, smc) =
             if addr `IS.member` populated
               then pure (as, addrs)
               else do a <- populateChunkAssumption (byteCache mpt) sym
                          (memPtrArray mpt) (IMI.lowerBound addr) smc
                       pure (a : as, addr : addrs)

       -- Populate mutable chunks, unless memModelContents is SymbolicMutable
       -- (in which case we leave mutable memory fully symbolic).
       acc0 <- if memModelContents mpt == MSMC.SymbolicMutable
               then pure ([], [])
               else let mutTbl = MSMC.getMutableIntervalMap (memMutableTable mpt)
                    in MSMC.pleatM ([], []) (ivals mutTbl) collectChunk

       -- For reads, also populate immutable chunks (needed in the SMT array
       -- for symbolic reads that fall through concreteUnmutatedGlobalRead).
       -- Writes don't need them since mkGlobalPointerValidityPred rejects
       -- writes to immutable memory.
       (assumps, newAddrs) <- case useTag of
         MS.PointerWrite -> pure acc0
         MS.PointerRead ->
           let immutTbl = MSMC.getImmutableIntervalMap (memImmutableTable mpt)
           in MSMC.pleatM acc0 (ivals immutTbl) collectChunk

       if null assumps
         then pure state
         else do gc <- CB.saveAssumptionState bak
                 let gc' = List.foldl' (\g a -> CBP.gcAddTopLevelAssume
                              (CB.singleAssumption a) g) gc assumps
                 CB.restoreAssumptionState bak gc'
                 pure $ L.over chunksL (<> IS.fromList newAddrs) state

  | otherwise
  = pure state
  where
    sym = CB.backendGetSym bak

    chunksL :: forall rtp f args.
               L.Lens' (CS.SimState p sym ext rtp f args)
                       (IS.IntervalSet (IMI.Interval (MC.MemWord w)))
    chunksL = CS.stateContext . CS.cruciblePersonality . MS.populatedMemChunks

{-
Note [Top-level assumptions]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~

When the lazy memory model loads from a chunk of global memory for the first
time, it creates an assumption that the memory in question holds its initial
value (see Note [Lazy memory model]). Unlike the non-lazy memory model,
this assumption can't simply be added to the Crucible symbolic backend using
`addAssumption`, as that method adds an assumption *along the current path*. In
other words, the assumption would only be in scope for proof obligations arising
along the current path. Instead, the assumption that the memory is initialized
should be in scope for *all* goals.

How can we achieve this? We ask the backend to export the state of
its assumptions (`saveAssumptionState`), add "top-level" assumptions
(`gcAddTopLevelAssume`), and restore the state (`restoreAssumptionState`).
For online backends, this will result in resetting the solver process and
re-asserting all of the in-scope assumptions. Since the restore is expensive, we
batch all newly-needed chunk assumptions and perform a single save/restore cycle
rather than one per chunk.
-}

-- | Build an assumption that constrains the SMT array backing global memory
-- to have the given bytes at the given address.
--
-- For concrete bytes, we map through the shared 'MBC.ByteCache' to obtain
-- symbolic byte literals without allocating fresh What4 expressions.
populateChunkAssumption ::
  forall sym t st fs w.
  ( sym ~ WEB.ExprBuilder t st fs
  , MC.MemWidth w
  ) =>
  MBC.ByteCache sym ->
  sym ->
  WI.SymArray sym (Ctx.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8) ->
  MC.MemWord w ->
  SymbolicMemChunk sym ->
  IO (CB.Assumption sym)
populateChunkAssumption cache sym symArray absAddr = \case
  ConcreteBytes bs ->
    MSMC.memArrEqualityAssumption sym symArray absAddr
      (map (MBC.indexByteCache cache) (BS.unpack bs))
  SymbolicBytes s ->
    MSMC.memArrEqualityAssumption sym symArray absAddr s

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
     , MSMC.MacawProcessAssertion sym
     )
  => MemPtrTable sym w
  -> MS.MkGlobalPointerValidityAssertion sym w
mkGlobalPointerValidityPred mpt =
  MSMC.mkGlobalPointerValidityPredCommon
    (memMutableTable mpt)
    (memImmutableTable mpt)

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
upfront is usually enough eat up all the RAM on your machine. And even if you
/do/ have enough RAM to handle the amount of space that an SMT solver would
need for such a query, it takes a staggering amount of time for the solver to
answer such a query. While it is not immediately obvious what causes this, some
related work on the subject of SMT array performance can be found in these
issues:

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
   case the memory gets updated, there's really no need to track the read-only
   global memory in an SMT array, nor to track writable memory that has not
   yet been mutated. We can determine what unmutated memory will be by looking
   up the corresponding bytes in the IntervalMap, bypassing the SMT array
   completely.

   To determine which parts of memory are read-only, each `SymbolicMemChunk`
   tracks whether its bytes are mutable or immutable. When performing a memory
   read, if we can conclude that all of the memory to be read is immutable
   (i.e., read-only) or not yet written, then we can convert the symbolic bytes
   to a bitvector. (See `readBytesAsRegValue` for how this is implemented.)

   There are several criteria that must be met in order for this to be
   possible:

   * The read must be concrete.

   * The amount of bytes to be read must lie within a contiguous part of
     unmutated memory.

   * There must be enough bytes within this part of memory to cover the number
     of bytes that must be read.

   If one of these critera are not met, we fall back on the SMT array approach.

Fundamentally, the lazy memory model sacrifices space (in the form of having to
track each byte of the global address space in the `memPtrTable`) in exchange
for fewer SMT array accesses at simulation time, which generally results in
better simulation-time performance as binary sizes increase. If SMT solvers
improve their performance with respect to arrays in the future, however, it is
possible that the default memory model could be a better choice. For this
reason, we provide both memory models as options.
-}
