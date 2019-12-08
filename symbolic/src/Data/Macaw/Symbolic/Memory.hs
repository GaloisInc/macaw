{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides a model implementation of a 'MS.GlobalMap'
--
-- The implementation is generic and should be suitable for most use cases.  The
-- documentation for 'MS.GlobalMap' describes the problem being solved in
-- detail.  At a high level, we need to map bitvector values to pointers in the
-- LLVM memory model.
--
-- This module provides an interface to populate an LLVM memory based on the
-- contents of the 'MC.Memory' object from macaw.  Read-only memory is mapped in
-- as immutable concrete data.  Mutable memory can be optionally mapped as
-- concrete or symbolic, depending on the use case required.  This model could
-- be extended to make the symbolic/concrete distinction more granular.
--
-- Below is an example of using this module to simulate a machine code function
-- using Crucible.
--
-- > {-# LANGUAGE DataKinds #-}
-- > {-# LANGUAGE FlexibleContexts #-}
-- > {-# LANGUAGE GADTs #-}
-- > {-# LANGUAGE ScopedTypeVariables #-}
-- > {-# LANGUAGE TypeApplications #-}
-- > {-# LANGUAGE TypeOperators #-}
-- >
-- > import           GHC.TypeLits
-- > import           Control.Monad.ST ( stToIO, RealWorld )
-- > import qualified Data.Macaw.CFG as MC
-- > import qualified Data.Macaw.Symbolic as MS
-- > import qualified Data.Macaw.Symbolic.Memory as MSM
-- > import           Data.Proxy ( Proxy(..) )
-- > import qualified Lang.Crucible.Backend as CB
-- > import qualified Lang.Crucible.CFG.Core as CC
-- > import qualified Lang.Crucible.FunctionHandle as CFH
-- > import qualified Lang.Crucible.LLVM.MemModel as CLM
-- > import qualified Lang.Crucible.LLVM.Intrinsics as CLI
-- > import qualified Lang.Crucible.LLVM.DataLayout as LDL
-- > import qualified Lang.Crucible.Simulator as CS
-- > import qualified Lang.Crucible.Simulator.GlobalState as CSG
-- > import qualified System.IO as IO
-- > import qualified What4.Interface as WI
-- >
-- > useCFG :: forall sym arch blocks
-- >         . ( CB.IsSymInterface sym
-- >           , MS.SymArchConstraints arch
-- >           , 16 <= MC.ArchAddrWidth arch
-- >           , Ord (WI.SymExpr sym WI.BaseNatType)
-- >           , KnownNat (MC.ArchAddrWidth arch)
-- >           )
-- >        => CFH.HandleAllocator RealWorld
-- >        -- ^ The handle allocator used to construct the CFG
-- >        -> sym
-- >        -- ^ The symbolic backend
-- >        -> MS.ArchVals arch
-- >        -- ^ 'ArchVals' from a prior call to 'archVals'
-- >        -> CS.RegMap sym (MS.MacawFunctionArgs arch)
-- >        -- ^ Initial register state for the simulation
-- >        -> MC.Memory (MC.ArchAddrWidth arch)
-- >        -- ^ The memory recovered by macaw
-- >        -> MS.LookupFunctionHandle sym arch
-- >        -- ^ A translator for machine code addresses to function handles
-- >        -> CC.CFG (MS.MacawExt arch) blocks (MS.MacawFunctionArgs arch) (MS.MacawFunctionResult arch)
-- >        -- ^ The CFG to simulate
-- >        -> IO ()
-- > useCFG hdlAlloc sym MS.ArchVals { MS.withArchEval = withArchEval }
-- >        initialRegs mem lfh cfg = withArchEval sym $ \archEvalFns -> do
-- >   let rep = CFH.handleReturnType (CC.cfgHandle cfg)
-- >   memModelVar <- stToIO (CLM.mkMemVar hdlAlloc)
-- >   (initialMem, memPtrTbl) <- MSM.newGlobalMemory (Proxy @arch) sym LDL.LittleEndian MSM.SymbolicMutable mem
-- >   let extImpl = MS.macawExtensions archEvalFns memModelVar (MSM.mapRegionPointers memPtrTbl) lfh
-- >   let simCtx = CS.initSimContext sym CLI.llvmIntrinsicTypes hdlAlloc IO.stderr CFH.emptyHandleMap extImpl MS.MacawSimulatorState
-- >   let simGlobalState = CSG.insertGlobal memModelVar initialMem CS.emptyGlobals
-- >   let simulation = CS.regValue <$> CS.callCFG cfg initialRegs
-- >   let initialState = CS.InitialState simCtx simGlobalState CS.defaultAbortHandler (CS.runOverrideSim rep simulation)
-- >   let executionFeatures = []
-- >   execRes <- CS.executeCrucible executionFeatures initialState
-- >   case execRes of
-- >     CS.FinishedResult {} -> return ()
-- >     _ -> putStrLn "Simulation failed"
-- >
module Data.Macaw.Symbolic.Memory (
  -- * Memory Management
  MemPtrTable,
  toCrucibleEndian,
  newGlobalMemory,
  MemoryModelContents(..),
  mapRegionPointers
  ) where

import           GHC.TypeLits

import           Control.Monad
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import qualified Data.IntervalMap.Strict as IM

import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.Interface as WI
import qualified What4.Symbol as WS

import qualified Data.Macaw.Symbolic as MS

import Prelude

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
data MemPtrTable sym w =
  MemPtrTable { memPtrTable :: IM.IntervalMap (MC.MemWord w) CL.Mutability
              -- ^ The ranges of (static) allocations that are mapped
              , memPtr :: CL.LLVMPtr sym w
              -- ^ The pointer to the allocation backing all of memory
              }

-- | Convert a Macaw Endianness to a Crucible LLVM EndianForm
toCrucibleEndian :: MC.Endianness -> CLD.EndianForm
toCrucibleEndian MC.BigEndian    = CLD.BigEndian
toCrucibleEndian MC.LittleEndian = CLD.LittleEndian

-- | Create a new LLVM memory model instance ('CL.MemImpl') and an index that
-- enables pointer translation ('MemPtrTable').  The contents of the
-- 'CL.MemImpl' are populated based on the 'MC.Memory' (macaw memory) passed in.
-- Read-only data is immutable and concrete.  Other data in the binary is mapped
-- in as either concrete or symbolic based on the value of the
-- 'MemoryModelContents' parameter.
newGlobalMemory :: ( 16 <= MC.ArchAddrWidth arch
                   , MC.MemWidth (MC.ArchAddrWidth arch)
                   , KnownNat (MC.ArchAddrWidth arch)
                   , CB.IsSymInterface sym
                   , Ord (WI.SymExpr sym WI.BaseNatType)
                   , MonadIO m
                   )
                => proxy arch
                -- ^ A proxy to fix the architecture
                -> sym
                -- ^ The symbolic backend used to construct terms
                -> CLD.EndianForm
                -- ^ The endianness of values in memory
                -> MemoryModelContents
                -- ^ A configuration option controlling how mutable memory should be represented (concrete or symbolic)
                -> MC.Memory (MC.ArchAddrWidth arch)
                -- ^ The macaw memory
                -> m (CL.MemImpl sym, MemPtrTable sym (MC.ArchAddrWidth arch))
newGlobalMemory proxy sym endian mmc mem = do
  let ?ptrWidth = MC.memWidth mem

  memImpl1 <- liftIO $ CL.emptyMem endian

  let allocName = WS.safeSymbol "globalMemoryBytes"
  symArray <- liftIO $ WI.freshConstant sym allocName CT.knownRepr
  sizeBV <- liftIO $ WI.maxUnsignedBV sym (MC.memWidth mem)
  (ptr, memImpl2) <- liftIO $ CL.doMalloc sym CL.GlobalAlloc CL.Mutable
                         "Global memory for macaw-symbolic"
                         memImpl1 sizeBV CLD.noAlignment
  memImpl3 <- liftIO $ CL.doArrayStore sym memImpl2 ptr CLD.noAlignment symArray sizeBV

  tbl <- populateMemory proxy sym mmc mem symArray
  let ptrTable = MemPtrTable { memPtrTable = tbl, memPtr = ptr }
  return (memImpl3, ptrTable)

populateMemory :: ( CB.IsSymInterface sym
                  , 16 <= MC.ArchAddrWidth arch
                  , MC.MemWidth (MC.ArchAddrWidth arch)
                  , KnownNat (MC.ArchAddrWidth arch)
                  , MonadIO m
                  )
               => proxy arch
               -- ^ A proxy to fix the architecture
               -> sym
               -- ^ The symbolic backend
               -> MemoryModelContents
               -- ^ A flag to indicate how to populate the memory model based on the memory image
               -> MC.Memory (MC.ArchAddrWidth arch)
               -- ^ The initial memory image for the binary, which contains static data to populate the memory model
               -> WI.SymArray sym (CT.SingleCtx (WI.BaseBVType (MC.ArchAddrWidth arch))) (WI.BaseBVType 8)
               -> m (IM.IntervalMap (MC.MemWord (MC.ArchAddrWidth arch)) CL.Mutability)
populateMemory proxy sym mmc mem symArray =
  pleatM IM.empty (MC.memSegments mem) $ \allocs1 seg -> do
    pleatM allocs1 (MC.relativeSegmentContents [seg]) $ \allocs2 (addr, memChunk) -> do
      concreteBytes <- case memChunk of
        MC.RelocationRegion {} -> error $
          "SymbolicRef SegmentRanges are not supported yet: " ++ show memChunk
        MC.BSSRegion sz ->
          liftIO $ replicate (fromIntegral sz) <$> WI.bvLit sym PN.knownNat 0
        MC.ByteRegion bytes ->
          liftIO $ mapM (WI.bvLit sym PN.knownNat . fromIntegral) $ BS.unpack bytes
      populateSegmentChunk proxy sym mmc mem symArray seg addr concreteBytes allocs2

-- | If we want to treat the contents of this chunk of memory (the bytes at the
-- 'MemAddr'), assert that the bytes from the symbolic array backing memory
-- match concrete values.  Otherwise, leave bytes as totally symbolic.
--
-- Note that this is populating memory for *part* of a segment, and not the
-- entire segment.  This is because segments can be stored as chunks of concrete
-- values.  The address is the address of a chunk and not a segment.
populateSegmentChunk :: ( 16 <= w
                      , MC.MemWidth w
                      , KnownNat w
                      , CB.IsSymInterface sym
                      , MonadIO m
                      , MC.ArchAddrWidth arch ~ w
                      )
                   => proxy arch
                   -> sym
                   -> MemoryModelContents
                   -- ^ The interpretation of mutable memory that we want to use
                   -> MC.Memory w
                   -- ^ The contents of memory
                   -> WI.SymArray sym (CT.SingleCtx (WI.BaseBVType (MC.ArchAddrWidth arch))) (WI.BaseBVType 8)
                   -- ^ The symbolic array backing memory
                   -> MC.MemSegment w
                   -- ^ The segment containing this chunk
                   -> MC.MemAddr w
                   -- ^ Memory chunk address
                   -> [WI.SymBV sym 8]
                   -- ^ The concrete values in this chunk (which may or may not be used)
                   -> IM.IntervalMap (MC.MemWord w) CL.Mutability
                   -> m (IM.IntervalMap (MC.MemWord w) CL.Mutability)
populateSegmentChunk _ sym mmc mem symArray seg addr bytes ptrtable = do
  -- We only support statically-linked binaries for now, so fail if we have a
  -- segment-relative address (which should only occur for an object file or
  -- shared library)
  let ?ptrWidth = MC.memWidth mem
  let Just abs_addr = MC.asAbsoluteAddr addr
  let size = length bytes
  let interval = IM.IntervalCO abs_addr (abs_addr + fromIntegral size)
  let (mut_flag, conc_flag, desc) =
        case MMP.isReadonly (MC.segmentFlags seg) of
          True ->
            ( CL.Immutable
            , True
            , \address -> "Mutable (concrete) memory at " ++ show address
            )
          False -> case mmc of
            ConcreteMutable ->
              ( CL.Mutable
              , True
              , \address -> "Mutable (concrete) memory at " ++ show address
              )
            SymbolicMutable ->
              ( CL.Mutable
              , False
              , \address -> "Mutable (symbolic) memory at " ++ show address
              )

  -- When we are treating a piece of memory as having concrete initial values
  -- (e.g., for read-only memory), this loop populates memory by asserting that
  -- the symbolic bytes in the backing array representing memory are equal to
  -- the concrete values taken from the binary.
  when conc_flag $
    F.forM_ (zip [0 .. size - 1] bytes) $ \(idx, byte) -> do
      let byteAddr = MC.incAddr (fromIntegral idx) addr
      -- FIXME: We can probably properly handle all of the different segments
      -- here pretty easily when required... but we will need one array per
      -- segment.
      let Just absByteAddr = MC.asAbsoluteAddr byteAddr
      index_bv <- liftIO $ WI.bvLit sym (MC.memWidth mem) (fromIntegral absByteAddr)
      eq_pred <- liftIO $ WI.bvEq sym byte
        =<< WI.arrayLookup sym symArray (Ctx.singleton index_bv)
      prog_loc <- liftIO $ WI.getCurrentProgramLoc sym
      liftIO $ CB.addAssumption sym $
        CB.LabeledPred eq_pred $ CB.AssumptionReason prog_loc (desc byteAddr)
  return (IM.insert interval mut_flag ptrtable)


-- | The 'pleatM' function is 'foldM' with the arguments switched so
-- that the function is last.
pleatM :: (Monad m, F.Foldable t)
       => b
       -> t a
       -> (b -> a -> m b)
       -> m b
pleatM s l f = F.foldlM f s l

-- * mapRegionPointers

-- | Construct a translator for machine addresses into LLVM memory model pointers.
--
-- This translator is used by the symbolic simulator to resolve memory addresses.
mapRegionPointers :: ( MC.MemWidth w
                     , 16 <= w
                     , CB.IsSymInterface sym
                     )
                  => MemPtrTable sym w
                  -> CL.LLVMPtr sym w
                  -> MS.GlobalMap sym w
mapRegionPointers mpt default_ptr = \sym mem regionNum offsetVal ->
  case WI.asNat regionNum of
    Just 0 -> mapBitvectorToLLVMPointer mpt sym mem offsetVal default_ptr
    Just _ ->
      -- This is the case where the region number is concrete and non-zero,
      -- meaning that it is already an LLVM pointer
      return (Just (CL.LLVMPointer regionNum offsetVal))
    Nothing ->
      -- In this case, the region number is symbolic, so we need to be very
      -- careful to handle the possibility that it is zero (and thus must be
      -- conditionally mapped to one or all of our statically-allocated regions.
      mapSymbolicRegionPointer mpt sym mem regionNum offsetVal default_ptr

-- | This is a relatively simple case where we know that the region number is
-- zero.  This means that the bitvector we have needs to be mapped to a pointer.
mapBitvectorToLLVMPointer :: ( MC.MemWidth w
                             , 16 <= w
                             , CB.IsSymInterface sym
                             )
                          => MemPtrTable sym w
                          -> sym
                          -> CS.RegValue sym CL.Mem
                          -> CS.RegValue sym (CT.BVType w)
                          -> CL.LLVMPtr sym w
                          -> IO (Maybe (CL.LLVMPtr sym w))
mapBitvectorToLLVMPointer mpt sym mem offsetVal default_ptr = do
  -- This is the simplest case where the bitvector is concretely known.  We
  -- can map it to exactly one address.
  --
  -- We already know that the region ID is 0 due to mapRegionPointers
  --
  -- It doesn't matter if the offset is symbolic or not because all of the
  -- static pointers are in this allocation somewhere.
  let ?ptrWidth = WI.bvWidth offsetVal
  -- FIXME: Assert that the resulting pointer is in the mapped range
  ptr <- CL.doPtrAddOffset sym mem (memPtr mpt) offsetVal
  return (Just ptr)

-- | Create a mux tree that maps the input bitvector (which is the offset in a
-- LLVMPointer with region == 0) to one of the regions that are statically
-- allocated (in the 'MemPtrTable').
--
-- Assume that there is an allocation A that covers [addrStart, addrEnd].  Also,
-- assume that the offset is some symbolic value O.  The mux tree says:
--
-- > "If addrStart <= O <= addrEnd, map O into that region"
--
-- If the offset is not in any region, the pointer is mapped to the null pointer
-- to trigger an error (if it is used).
staticRegionMuxTree :: ( CB.IsSymInterface sym
                       , MC.MemWidth w
                       , 16 <= w
                       )
                    => MemPtrTable sym w
                    -> sym
                    -> CL.MemImpl sym
                    -> WI.SymExpr sym (WI.BaseBVType w)
                    -> CL.LLVMPtr sym w
                    -> IO (CL.LLVMPtr sym w)
staticRegionMuxTree mpt@(MemPtrTable im _) sym mem offsetVal default_ptr =
  case IM.toList im of
    [] -> return default_ptr
    [_] -> do
      let ?ptrWidth = WI.bvWidth offsetVal
      -- FIXME: Assert that the resulting pointer is in the mapped range
      CL.doPtrAddOffset sym mem (memPtr mpt) offsetVal
    _regions -> do
      -- FIXME: This case needs to be much more sophisticated
      let ?ptrWidth = WI.bvWidth offsetVal
      -- FIXME: Assert that the resulting pointer is in the mapped range
      CL.doPtrAddOffset sym mem (memPtr mpt) offsetVal
      -- This is needs to be able to mux over other allocations?  I'm not sure on how
      -- the symbolic array model actually works

               -- F.foldlM addMuxForRegion default_ptr (IM.toList im)
  -- where
    -- handleCase f alloc start end greater less = do
    --   let rep = WI.bvWidth offsetVal
    --   startLit <- WI.bvLit sym rep (MC.memWordToUnsigned start)
    --   endLit <- WI.bvLit sym rep (MC.memWordToUnsigned end)
    --   gt <- greater sym offsetVal startLit
    --   lt <- less sym offsetVal endLit
    --   p <- WI.andPred sym gt lt
    --   allocBase <- WI.bvLit sym rep (MC.memWordToUnsigned (allocationBase alloc))
    --   allocationOffset <- WI.bvSub sym offsetVal allocBase
    --   let ?ptrWidth = rep
    --   thisPtr <- CL.doPtrAddOffset sym mem (allocationPtr alloc) allocationOffset
    --   CL.muxLLVMPtr sym p thisPtr f
    -- addMuxForRegion f (interval, alloc) = do
    --   case interval of
    --     IM.IntervalOC start end -> handleCase f alloc start end WI.bvUgt WI.bvUle
    --     IM.IntervalCO start end -> handleCase f alloc start end WI.bvUge WI.bvUlt
    --     IM.ClosedInterval start end -> handleCase f alloc start end WI.bvUge WI.bvUle
    --     IM.OpenInterval start end -> handleCase f alloc start end WI.bvUgt WI.bvUlt

-- | This is a potentially complicated case where the region number is symbolic.
-- We need to add some guards in the cases where it is zero, to allow it to be
-- mapped to one of our regions.  When it is not zero, we can leave it alone.
mapSymbolicRegionPointer :: ( MC.MemWidth w
                            , 16 <= w
                            , CB.IsSymInterface sym
                            )
                         => MemPtrTable sym w
                         -> sym
                         -> CS.RegValue sym CL.Mem
                         -> CS.RegValue sym CT.NatType
                         -> CS.RegValue sym (CT.BVType w)
                         -> CL.LLVMPtr sym w
                         -> IO (Maybe (CL.LLVMPtr sym w))
mapSymbolicRegionPointer mpt sym mem regionNum offsetVal default_ptr = do
  zeroNat <- WI.natLit sym 0
  staticRegion <- staticRegionMuxTree mpt sym mem offsetVal default_ptr
  isZeroRegion <- WI.natEq sym zeroNat regionNum
  let nonZeroPtr = CL.LLVMPointer regionNum offsetVal
  Just <$> CL.muxLLVMPtr sym isZeroRegion staticRegion nonZeroPtr
