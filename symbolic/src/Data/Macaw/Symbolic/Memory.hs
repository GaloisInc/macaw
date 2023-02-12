{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides model implementations of 'MS.GlobalMap' and 'MS.MkGlobalPointerValidityPred'
--
-- The implementation is generic and should be suitable for most use cases.  The
-- documentation for 'MS.GlobalMap' describes the problem being solved in
-- detail.  At a high level, we need to map bitvector values to pointers in the
-- LLVM memory model.
--
-- This module provides an interface to populate an LLVM memory model from the
-- contents of the 'MC.Memory' object from macaw.  All of the static memory in a
-- binary is mapped into a single "symbolic" memory allocation in the LLVM
-- memory model.  The allocation is symbolic in that it is backed by a symbolic
-- SMT array.  Bytes in the symbolic allocation are initialized with concrete
-- data if they are read-only data (e.g., from .rodata or the .text sections).
-- Optionally, mutable data can be included in the initialization (see
-- 'MemoryModelContents').  The 'MS.MkGlobalPointerValidityPred' function can be
-- used to enforce that writes do not clobber read-only data and that no reads
-- or writes touch unmapped memory.
--
-- This module does not represent the only possible memory model.  It just
-- provides a default implementation that should be generally useful.
--
-- Note that representing all static memory in a single allocation (and thus SMT
-- array) is intended to improve efficiency by pushing as much pointer reasoning
-- as possible into the theory of arrays.  This formulation enables efficient
-- handling of symbolic reads and writes when they are sufficiently constrained
-- by predicates in the program.
--
-- Below is an example of using this module to simulate a machine code function
-- using Crucible.
--
-- >>> :set -XDataKinds
-- >>> :set -XFlexibleContexts
-- >>> :set -XGADTs
-- >>> :set -XImplicitParams
-- >>> :set -XOverloadedStrings
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> :set -XTypeOperators
-- >>> import           GHC.TypeLits
-- >>> import           Data.IORef
-- >>> import qualified Data.Macaw.CFG as MC
-- >>> import qualified Data.Macaw.Symbolic as MS
-- >>> import qualified Data.Macaw.Symbolic.Memory as MSM
-- >>> import           Data.Proxy ( Proxy(..) )
-- >>> import qualified Lang.Crucible.Backend as CB
-- >>> import qualified Lang.Crucible.CFG.Core as CC
-- >>> import qualified Lang.Crucible.FunctionHandle as CFH
-- >>> import qualified Lang.Crucible.LLVM.MemModel as CLM
-- >>> import qualified Lang.Crucible.LLVM.Intrinsics as CLI
-- >>> import qualified Lang.Crucible.LLVM.DataLayout as LDL
-- >>> import qualified Lang.Crucible.Simulator as CS
-- >>> import qualified Lang.Crucible.Simulator.GlobalState as CSG
-- >>> import qualified System.IO as IO
-- >>> import qualified What4.Interface as WI
-- >>> :{
-- useCFG :: forall sym arch blocks
--         . ( CB.IsSymInterface sym
--           , MS.SymArchConstraints arch
--           , 16 <= MC.ArchAddrWidth arch
--           , Ord (WI.SymExpr sym WI.BaseIntegerType)
--           , KnownNat (MC.ArchAddrWidth arch)
--           )
--        => CFH.HandleAllocator
--        -- ^ The handle allocator used to construct the CFG
--        -> sym
--        -- ^ The symbolic backend
--        -> MS.ArchVals arch
--        -- ^ 'ArchVals' from a prior call to 'archVals'
--        -> CS.RegMap sym (MS.MacawFunctionArgs arch)
--        -- ^ Initial register state for the simulation
--        -> MC.Memory (MC.ArchAddrWidth arch)
--        -- ^ The memory recovered by macaw
--        -> MS.LookupFunctionHandle sym arch
--        -- ^ A translator for machine code addresses to function handles
--        -> CC.CFG (MS.MacawExt arch) blocks (MS.MacawFunctionArgs arch) (MS.MacawFunctionResult arch)
--        -- ^ The CFG to simulate
--        -> IO ()
-- useCFG hdlAlloc sym avals initialRegs mem lfh cfg =
--   let ?recordLLVMAnnotation = \_ _ -> (pure () :: IO ())
--   in MS.withArchEval avals sym $ \archEvalFns -> do
--     let rep = CFH.handleReturnType (CC.cfgHandle cfg)
--     memModelVar <- CLM.mkMemVar "macaw:llvm_memory" hdlAlloc
--     (initialMem, memPtrTbl) <- MSM.newGlobalMemory (Proxy @arch) sym LDL.LittleEndian MSM.SymbolicMutable mem
--     let mkValidityPred = MSM.mkGlobalPointerValidityPred memPtrTbl
--     let extImpl = MS.macawExtensions archEvalFns memModelVar (MSM.mapRegionPointers memPtrTbl) lfh mkValidityPred
--     let simCtx = CS.initSimContext sym CLI.llvmIntrinsicTypes hdlAlloc IO.stderr (CS.FnBindings CFH.emptyHandleMap) extImpl MS.MacawSimulatorState
--     let simGlobalState = CSG.insertGlobal memModelVar initialMem CS.emptyGlobals
--     let simulation = CS.regValue <$> CS.callCFG cfg initialRegs
--     let initialState = CS.InitialState simCtx simGlobalState CS.defaultAbortHandler rep (CS.runOverrideSim rep simulation)
--     let executionFeatures = []
--     execRes <- CS.executeCrucible executionFeatures initialState
--     case execRes of
--       CS.FinishedResult {} -> return ()
--       _ -> putStrLn "Simulation failed"
-- :}
module Data.Macaw.Symbolic.Memory (
  -- * Global Pointers
  PointerUse(..),
  PointerUseTag(..),
  pointerUseLocation,
  pointerUseTag,
  MkGlobalPointerValidityAssertion,
  -- * Memory Management
  MemPtrTable,
  SymbolicMemChunk,
  combineSymbolicMemChunks,
  combineIfContiguous,
  combineChunksIfContiguous,
  toCrucibleEndian,
  fromCrucibleEndian,
  newMemPtrTable,
  GlobalMemoryHooks(..),
  defaultGlobalMemoryHooks,
  MemoryModelContents(..),
  mkGlobalPointerValidityPred,
  mapRegionPointers,
  readBytesAsRegValue
  ) where

import           GHC.TypeLits

import qualified Control.Exception as X
import qualified Control.Lens as L
import           Control.Monad
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.BitVector.Sized as BV
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import           Data.Functor.Identity ( Identity(Identity) )
import qualified Data.IntervalMap.Interval as IMI
import qualified Data.IntervalMap.Strict as IM
import qualified Data.List.Split as Split
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Vector as PV
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Sequence as Seq
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.MemModel.Pointer as CLP
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import           Text.Printf ( printf )
import qualified What4.Expr.App as WEA
import qualified What4.Expr.BoolMap as BoolMap
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WPL
import qualified What4.Symbol as WS

import qualified Data.Macaw.Symbolic.MemOps as MSMO
import qualified Data.Macaw.Symbolic.PersistentState as MSP

import Prelude

-- TODO RGS: Is this the best home for these types?

-- | A use of a pointer in a memory operation
--
-- Uses can be reads or writes (see 'PointerUseTag').  The location is used to
-- produce diagnostics where possible.
data PointerUse = PointerUse (Maybe WPL.ProgramLoc) PointerUseTag

-- | Tag a use of a pointer ('PointerUse') as a read or a write
data PointerUseTag = PointerRead | PointerWrite
  deriving (Eq, Show)

-- | Extract a location from a 'PointerUse', defaulting to the initial location
-- if none was provided
pointerUseLocation :: PointerUse -> WPL.ProgramLoc
pointerUseLocation (PointerUse mloc _) =
  case mloc of
    Just loc -> loc
    Nothing -> WPL.initializationLoc

-- | Extract the tag denoting a 'PointerUse' as a read or a write
pointerUseTag :: PointerUse -> PointerUseTag
pointerUseTag (PointerUse _ tag) = tag

-- | A function to construct validity predicates for pointer uses
--
-- This function creates an assertion that encodes the validity of a global
-- pointer.  One of the intended use cases is that this can be used to generate
-- assertions that memory accesses are limited to some mapped range of memory.
-- It could also be used to prohibit reads from or writes to distinguished
-- regions of the address space.
--
-- Note that macaw-symbolic is agnostic to the semantics of the produced
-- assertion.  A verification tool could simply use @return Nothing@ as the
-- implementation to elide extra memory safety checks, or if they are not
-- required for the desired memory model.
type MkGlobalPointerValidityAssertion sym w = sym
                                            -- ^ The symbolic backend in use
                                            -> PointerUse
                                            -- ^ A tag marking the pointer use as a read or a write
                                            -> Maybe (CS.RegEntry sym CT.BoolType)
                                            -- ^ If this is a conditional read or write, the predicate
                                            -- determining whether or not the memory operation is executed.  If
                                            -- generating safety assertions, they should account for the presence and
                                            -- value of this predicate.
                                            -> CS.RegEntry sym (CL.LLVMPointerType w)
                                            -- ^ The address written to or read from
                                            -> IO (Maybe (CB.Assertion sym))

-- | A configuration knob controlling how the initial contents of the memory
-- model are populated
--
-- The fundamental question is how to treat global data.  It is (generally) safe
-- to make read only data concrete, as it cannot change during normal execution
-- (ignoring cases where the program uses mprotect or similar calls to change
-- memory permissions at runtime).
--
-- If we are trying to prove properties about functions in isolation, though, we
-- have to assume that non-constant global data can have /any/ value, which
-- means that we have to represent each byte as symbolic.  This will change when
-- we start pursuing compositional verification and want to have more elaborate
-- memory setups.
--
-- Note that using concrete mutable data from the binary image is unsafe, but
-- may be useful in some cases.
data MemoryModelContents = SymbolicMutable
                         -- ^ All mutable global data is fully symbolic, but
                         -- read-only data is concrete (and taken from the
                         -- memory image of the binary)
                         | ConcreteMutable
                         -- ^ All of the global data is taken from the binary

-- | An index of all of the (statically) mapped memory in a program, suitable
-- for pointer translation
--
-- TODO RGS: Revise Haddocks
data MemPtrTable sym w =
  MemPtrTable { memPtrTable :: IM.IntervalMap (MC.MemWord w) (SymbolicMemChunk sym)
              -- ^ The ranges of (static) allocations that are mapped
              , memPtr :: CL.LLVMPtr sym w
              -- ^ The pointer to the allocation backing all of memory
              , memPtrArray :: WI.SymArray sym (Ctx.SingleCtx (WI.BaseBVType w)) (WI.BaseBVType 8)
              -- ^ The SMT array mapping addresses to symbolic bytes
              }

-- | A discrete chunk of a memory segment within global memory. Memory is
-- lazily initialized one 'SymbolicMemChunk' at a time. See
-- @Note [Lazy memory initialization]@.
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

-- | Create a new 'MemPtrTable'. The type signature for this function is very
-- similar to that of 'DMS.newGlobalMemory' in @macaw-symbolic@, but unlike
-- that function, this one does not initialize the array backing the
-- 'MemPtrTable'. Instead, the initialization is deferred until simulation
-- begins. See @Note [Lazy memory initialization]@.
--
-- TODO RGS: Revise Haddocks
newMemPtrTable ::
    forall sym bak m t w
  . ( 16 WI.<= w
    , MC.MemWidth w
    , KnownNat w
    , CB.IsSymBackend sym bak
    , CL.HasLLVMAnn sym
    , MonadIO m
    , ?memOpts :: CL.MemOptions
    , Traversable t
    )
 => GlobalMemoryHooks w
 -- ^ Hooks customizing the memory setup
 -> bak
 -- ^ The symbolic backend used to construct terms
 -> CLD.EndianForm
 -- ^ The endianness of values in memory
 -> t (MC.Memory w)
 -- ^ The macaw memories
 -> m (CL.MemImpl sym, MemPtrTable sym w)
newMemPtrTable hooks bak endian mems = do
  let sym = CB.backendGetSym bak
  let ?ptrWidth = MC.memWidthNatRepr @w

  memImpl1 <- liftIO $ CL.emptyMem endian

  let allocName = WI.safeSymbol "globalMemoryBytes"
  symArray <- liftIO $ WI.freshConstant sym allocName WI.knownRepr
  sizeBV <- liftIO $ WI.maxUnsignedBV sym ?ptrWidth
  (ptr, memImpl2) <- liftIO $ CL.doMalloc bak CL.GlobalAlloc CL.Mutable
                         "Global memory for macaw-symbolic"
                         memImpl1 sizeBV CLD.noAlignment

  tbl <- liftIO $ mergedMemorySymbolicMemChunks bak hooks mems
  memImpl3 <- liftIO $ CL.doArrayStore bak memImpl2 ptr CLD.noAlignment symArray sizeBV
  let memPtrTbl = MemPtrTable { memPtrTable = tbl
                              , memPtr = ptr
                              , memPtrArray = symArray
                              }
  pure (memImpl3, memPtrTbl)

-- | Construct an 'IM.IntervalMap' mapping regions of memory to their bytes,
-- representing as 'SymbolicMemChunk's. The regions of memory are split apart
-- to be in units no larger than 'chunkSize' bytes.
-- See @Note [Lazy memory initialization]@.
--
-- TODO RGS: Revise Haddocks
mergedMemorySymbolicMemChunks ::
  forall sym bak t w.
  ( CB.IsSymBackend sym bak
  , MC.MemWidth w
  , Traversable t
  ) =>
  bak ->
  GlobalMemoryHooks w ->
  t (MC.Memory w) ->
  IO (IM.IntervalMap (MC.MemWord w) (SymbolicMemChunk sym))
mergedMemorySymbolicMemChunks bak hooks mems =
  fmap (IM.fromList . concat) $ traverse memorySymbolicMemChunks mems
  where
    sym = CB.backendGetSym bak
    w8 = WI.knownNat @8

    memorySymbolicMemChunks ::
      MC.Memory w ->
      IO [(IM.Interval (MC.MemWord w), SymbolicMemChunk sym)]
    memorySymbolicMemChunks mem = concat <$>
      traverse (segmentSymbolicMemChunks mem) (MC.memSegments mem)

    segmentSymbolicMemChunks ::
      MC.Memory w ->
      MC.MemSegment w ->
      IO [(IM.Interval (MC.MemWord w), SymbolicMemChunk sym)]
    segmentSymbolicMemChunks mem seg = concat <$>
      traverse
        (\(addr, chunk) -> do
          allBytes <- mkSymbolicMemChunkBytes mem seg addr chunk
          -- TODO RGS: Factor in ConcreteMutable/SymbolicMutable?
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

    mkSymbolicMemChunkBytes ::
         MC.Memory w
      -> MC.MemSegment w
      -> MC.MemAddr w
      -> MC.MemChunk w
      -> IO [WI.SymBV sym 8]
    mkSymbolicMemChunkBytes mem seg addr memChunk =
      liftIO $ case memChunk of
        MC.RelocationRegion reloc ->
          populateRelocation hooks bak mem seg addr reloc
        MC.BSSRegion sz ->
          replicate (fromIntegral sz) <$> WI.bvLit sym w8 (BV.zero w8)
        MC.ByteRegion bytes ->
          traverse (WI.bvLit sym w8 . BV.word8) $ BS.unpack bytes

-- | The maximum size of a 'SymbolicMemChunk', which determines the granularity
-- at which the regions of memory in a 'memPtrTable' are chunked up.
-- See @Note [Lazy memory initialization]@.
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

-- | Convert a Macaw 'MC.Endianness' to a Crucible LLVM 'CLD.EndianForm'.
toCrucibleEndian :: MC.Endianness -> CLD.EndianForm
toCrucibleEndian MC.BigEndian    = CLD.BigEndian
toCrucibleEndian MC.LittleEndian = CLD.LittleEndian

-- | Convert a Crucible LLVM 'CLD.EndianForm' to a Macaw 'MC.Endianness'.
fromCrucibleEndian :: CLD.EndianForm -> MC.Endianness
fromCrucibleEndian CLD.BigEndian    = MC.BigEndian
fromCrucibleEndian CLD.LittleEndian = MC.LittleEndian

-- | Hooks to configure the initialization of global memory
data GlobalMemoryHooks w =
  GlobalMemoryHooks {
  populateRelocation
    :: forall sym bak
       . (CB.IsSymBackend sym bak)
    => bak
    -> MC.Memory w
    -- ^ The region of memory in which the relocation is defined
    -> MC.MemSegment w
    -- ^ The segment of memory in which the relocation is defined
    -> MC.MemAddr w
    -- ^ The address of the relocation
    -> MC.Relocation w
    -> IO [WI.SymExpr sym (WI.BaseBVType 8)]
    -- ^ The symbolic bytes to represent a relocation with
    --
    -- They could be entirely unconstrained bytes, or could be distinguished
    -- bytes used to implement linking of shared libraries (i.e., relocation
    -- resolution)
  }

-- | A default set of hooks
--
-- These are used by 'newGlobalMemory', and may raise errors if they encounter
-- constructs that they do not handle (because there is no sensible default behavior).
defaultGlobalMemoryHooks :: GlobalMemoryHooks w
defaultGlobalMemoryHooks =
  GlobalMemoryHooks {
    populateRelocation = \_ _ _ _ r ->
      return (error ("SymbolicRef SegmentRanges are not supported yet: " ++ show r))
    }

-- | The 'pleatM' function is 'foldM' with the arguments switched so
-- that the function is last.
pleatM :: (Monad m, F.Foldable t)
       => b
       -> t a
       -> (b -> a -> m b)
       -> m b
pleatM s l f = F.foldlM f s l

-- * mapRegionPointers

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
mkGlobalPointerValidityPred :: forall sym w
                             . ( CB.IsSymInterface sym
                               , MC.MemWidth w
                               )
                            => MemPtrTable sym w
                            -> MkGlobalPointerValidityAssertion sym w
mkGlobalPointerValidityPred mpt = \sym puse mcond ptr -> do
  let w = MC.memWidthNatRepr @w

  -- If this is a write, the pointer cannot be in an immutable range (so just
  -- return False for the predicate on that range).
  --
  -- Otherwise, the pointer is allowed to be between the lo/hi range
  let inMappedRange off (range, mut)
        | pointerUseTag puse == PointerWrite && mut == CL.Immutable = return (WI.falsePred sym)
        | otherwise =
          case range of
            IM.IntervalCO lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUlt sym lobv off
              hib <- WI.bvUle sym off hibv
              WI.andPred sym lob hib
            IM.ClosedInterval lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUlt sym lobv off
              hib <- WI.bvUlt sym off hibv
              WI.andPred sym lob hib
            IM.OpenInterval lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUle sym lobv off
              hib <- WI.bvUle sym off hibv
              WI.andPred sym lob hib
            IM.IntervalOC lo hi -> do
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUle sym lobv off
              hib <- WI.bvUlt sym off hibv
              WI.andPred sym lob hib

  let mkPred off = do
        ps <- mapM (inMappedRange off) $ IM.toList $ fmap smcMutability $ memPtrTable mpt
        ps' <- WI.orOneOf sym (L.folded . id) ps
        -- Add the condition from a conditional write
        WI.itePred sym (maybe (WI.truePred sym) CS.regValue mcond) ps' (WI.truePred sym)


  let ptrVal = CS.regValue ptr
  let (ptrBase, ptrOff) = CL.llvmPointerView ptrVal
  case WI.asNat ptrBase of
    Just 0 -> do
      p <- mkPred ptrOff
      let msg = printf "%s outside of static memory range (known BlockID 0): %s" (show (pointerUseTag puse)) (show (WI.printSymExpr ptrOff))
      let loc = pointerUseLocation puse
      let assertion = CB.LabeledPred p (CS.SimError loc (CS.GenericSimError msg))
      return (Just assertion)
    Just _ -> return Nothing
    Nothing -> do
      -- In this case, we don't know for sure if the block id is 0, but it could
      -- be (it is symbolic).  The assertion has to be conditioned on the equality.
      p <- mkPred ptrOff
      zeroNat <- WI.natLit sym 0
      isZeroBase <- WI.natEq sym zeroNat ptrBase
      p' <- WI.itePred sym isZeroBase p (WI.truePred sym)
      let msg = printf "%s outside of static memory range (unknown BlockID): %s" (show (pointerUseTag puse)) (show (WI.printSymExpr ptrOff))
      let loc = pointerUseLocation puse
      let assertion = CB.LabeledPred p' (CS.SimError loc (CS.GenericSimError msg))
      return (Just assertion)

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
                  -> MSMO.GlobalMap sym CL.Mem w
mapRegionPointers mpt = MSMO.GlobalMap $ \bak mem regionNum offsetVal ->
  let sym = CB.backendGetSym bak in
  case WI.asNat regionNum of
    Just 0 -> do
      let ?ptrWidth = WI.bvWidth offsetVal
      CL.doPtrAddOffset bak mem (memPtr mpt) offsetVal
    Just _ ->
      -- This is the case where the region number is concrete and non-zero,
      -- meaning that it is already an LLVM pointer
      --
      -- NOTE: This case is not possible because we only call this from
      -- 'tryGlobPtr', which handles this case separately
      return (CL.LLVMPointer regionNum offsetVal)
    Nothing -> do
      -- In this case, the region number is symbolic, so we need to be very
      -- careful to handle the possibility that it is zero (and thus must be
      -- conditionally mapped to one or all of our statically-allocated regions.
      --
      -- NOTE: We can avoid making a huge static mux over all regions: the
      -- low-level memory model code already handles building the mux tree as it
      -- walks backwards over all allocations that are live.
      --
      -- We just need to add one top-level mux:
      --
      -- > ite (blockid == 0) (translate base) (leave alone)
      let ?ptrWidth = WI.bvWidth offsetVal
      zeroNat <- WI.natLit sym 0
      isZeroRegion <- WI.natEq sym zeroNat regionNum
      -- The pointer mapped to global memory (if the region number is zero)
      globalPtr <- CL.doPtrAddOffset bak mem (memPtr mpt) offsetVal
      CL.muxLLVMPtr sym isZeroRegion globalPtr (CL.LLVMPointer regionNum offsetVal)

-- Return @Just bytes@ if we can be absolutely sure that this is a concrete
-- read from a contiguous region of immutable, global memory, where @bytes@
-- are the bytes backing the global memory. Return @Nothing@ otherwise.
-- See @Note [Lazy memory initialization]@ in Ambient.Extensions.Memory.
--
-- TODO RGS: Revise Haddocks
concreteImmutableGlobalRead ::
  (CB.IsSymInterface sym, MC.MemWidth w) =>
  MC.MemRepr ty ->
  CL.LLVMPtr sym w ->
  MemPtrTable sym w ->
  Maybe [WI.SymBV sym 8]
concreteImmutableGlobalRead memRep ptr mpt
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
  = let bytes = Seq.take numBytes $
                Seq.drop addrOffset $
                smcBytes smc in
    Just $ F.toList bytes

  | otherwise
  = Nothing
  where
    numBytes = fromIntegral $ MC.memReprBytes memRep
    (ptrBlk, ptrOff) = CL.llvmPointerView ptr
    memPtrBlk = CLP.llvmPointerBlock (memPtr mpt)

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
  IO (CS.RegValue sym (MSP.ToCrucibleType ty))
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
-- immutable global memory. See @Note [Lazy memory initialization]@.
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
    -- things typecheck. The details of the type-level arithmetic were copied
    -- from PATE (https://github.com/GaloisInc/pate/blob/815d906243fef33993e340b8965567abe5bfcde0/src/Pate/Memory/MemTrace.hs#L1204-L1229),
    -- which is licensed under the 3-Clause BSD license.
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

-- Additional proof combinators

mulMono :: forall p q x w. (1 WI.<= x, 1 WI.<= w) => p x -> q w -> WI.LeqProof 1 (x WI.* w)
mulMono x w = WI.leqTrans (WI.LeqProof @1 @w) (WI.leqMulMono x w)

zeroSubEq :: forall p q w n. (n WI.<= w, 0 ~ (w WI.- n)) => p w -> q n -> w WI.:~: n
zeroSubEq w n
  | WI.Refl <- WI.minusPlusCancel w n
  = WI.Refl

{-
Note [Lazy memory initialization]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We back the global memory in a binary with an SMT array of symbolic bytes. One
issue with this approach is that initializing the elements of this array is
expensive. Despite our best efforts to optimize how SMT array initialization
takes places, filling in each byte of a large (i.e., several megabytes or more)
binary upfront is usually enough eat up all the RAM on your machine.

For this reason, we deliberately avoid populating the entire array upfront.
Instead, we initialize memory lazily. Here is a first approximation of how this
works:

* When the verifier starts, we create an empty SMT array to back global memory
  but do not initialize any of its elements. (See `newMemPtrTable` for how this
  is implemented.) We store this array in a MemPtrTable for later use.

* At the same time, we also store an IntervalMap in the MemPtrTable
  that maps the addresses in each memory segment to the corresponding bytes.
  (See the `SymbolicMemChunk` data type, which stores these bytes.)

* During simulation, if we attempt to access global memory, we first check
  to see if we have previously accessed the memory segment(s) corresponding to
  the addresses that were are accessing. If we haven't, we then initialize the
  bytes corresponding to those memory segments (and _only_ those memory
  segments) in the SMT array. We then record the fact that we have accessed
  these segments in the `populatedMemChunks` field of the
  `AmbientSimulatorState`.

* How do we determine which memory segments correspond to a particular read or
  write? If it is a concrete read or write, this is straightforward, as we need
  only look up a single address in the IntervalMap. If it is a symbolic read or
  write, then things are trickier, since it could potentially access different
  memory regions. To accommodate this, we construct an interval spanning all of
  the possible addresses that the read/write could access (see
  Ambient.Extensions.ptrOffsetInterval and retrieve all parts of the
  IntervalMap that intersect with the interval. This is costly, but it ensures
  that the approach is sound.

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

At some point, we would like to upstream this work to macaw-symbolic, as
nothing here is specific to AMBIENT. See
https://github.com/GaloisInc/macaw/issues/282. Much of the code that implements
was copied from macaw-symbolic itself, which is licensed under the 3-Clause BSD
license.
-}
