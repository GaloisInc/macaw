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
  newGlobalMemory,
  MemoryModelContents(..),
  mapRegionPointers,
  lookupAllocationBase,
  -- * Allocations
  Allocation,
  allocationBase,
  allocationPtr
  ) where

import           GHC.TypeLits

import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import qualified Data.IntervalMap.Strict as IM
import qualified Data.Map.Strict as Map
import qualified Data.Vector as V

import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.UndefinedBehavior as UB
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Types as CT
import qualified What4.Interface as WI

import qualified Data.Macaw.Symbolic as MS

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

-- | A wrapper around an LLVM memory model pointer with enough metadata to do
-- address translation from raw bitvectors (LLVM pointers with region 0) and
-- 'MM.MemAddr' values into 'MMP.LLVMPtr' values.
data Allocation sym w =
  Allocation { allocationPtr :: CL.LLVMPtr sym w
             -- ^ The LLVM memory model pointer that points to the memory
             -- allocated
             , allocationBase :: MC.MemWord w
             -- ^ The address of the base of the segment corresponding to this
             -- memory allocation
             }

-- | An index of all of the (statically) mapped memory in a program, suitable
-- for pointer translation
data MemPtrTable sym w =
  MemPtrTable { memPtrTable :: IM.IntervalMap (MC.MemWord w) (Allocation sym w)
              , allocationIndex :: Map.Map (CS.RegValue sym CT.NatType) (Allocation sym w)
              }

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
  memImpl1 <- liftIO $ CL.emptyMem endian
  (memImpl2, tbl) <- populateMemory proxy sym mmc mem memImpl1
  return (memImpl2, MemPtrTable { memPtrTable = tbl
                                , allocationIndex = indexAllocations tbl
                                })

-- | Set up the memory model with some initial contents based on the memory image of the binary
--
-- The strategy is configurable via the 'MemoryModelContents' parameter.  We
-- always leave read-only data as concrete and immutable.  We can either
-- instantiate mutable memory as concrete or symbolic.
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
               -> CL.MemImpl sym
               -- ^ The initial memory model (e.g., it might have a stack allocated)
               -> m (CL.MemImpl sym, IM.IntervalMap (MC.MemWord (MC.ArchAddrWidth arch)) (Allocation sym (MC.ArchAddrWidth arch)))
populateMemory _ sym mmc mem memImpl0 = do
  memImpl1 <- pleatM (memImpl0, IM.empty) (MC.memSegments mem) $ \impl1 seg -> do
    pleatM impl1 (MC.relativeSegmentContents [seg]) $ \impl2 (addr, memChunk) ->
      case memChunk of
        MC.RelocationRegion {} -> error ("SymbolicRef SegmentRanges are not supported yet: " ++ show memChunk)
        MC.BSSRegion sz -> do
          nzero <- liftIO $ WI.natLit sym 0
          bvzero <- liftIO $ WI.bvLit sym (PN.knownNat @8) 0
          let val = CL.LLVMValArray (CL.bitvectorType 1) (V.fromList (replicate (fromIntegral sz) (CL.LLVMValInt nzero bvzero)))
          addValueAt sym mmc mem seg addr sz val impl2
        MC.ByteRegion bytes -> do
          let sz = BS.length bytes
          nzero <- liftIO $ WI.natLit sym 0
          let fromWord8 w = do
                llw <- liftIO $ WI.bvLit sym (PN.knownNat @8) (fromIntegral w)
                return (CL.LLVMValInt nzero llw)
          llvmWords <- mapM fromWord8 (BS.unpack bytes)
          let val = CL.LLVMValArray (CL.bitvectorType 1) (V.fromList llvmWords)
          addValueAt sym mmc mem seg addr sz val impl2
  return memImpl1

-- | Add a new value (which is an LLVM array of bytes) of a given length at the given address.
addValueAt :: ( 16 <= w
              , MC.MemWidth w
              , KnownNat w
              , Integral a
              , Show a
              , CB.IsSymInterface sym
              , MonadIO m
              )
           => sym
           -> MemoryModelContents
           -> MC.Memory w
           -> MC.MemSegment w
           -> MC.MemAddr w
           -> a
           -> CL.LLVMVal sym
           -> (CL.MemImpl sym, IM.IntervalMap (MC.MemWord w) (Allocation sym w))
           -> m (CL.MemImpl sym, IM.IntervalMap (MC.MemWord w) (Allocation sym w))
addValueAt sym mmc mem seg addr sz val (impl, ptrtable) = do
  -- We only support statically-linked binaries for now, so fail if we have a
  -- segment-relative address (which should only occur for an object file or
  -- shared library)
  let Just absAddr = MC.asAbsoluteAddr addr
  let ty = CL.arrayType (fromIntegral sz) (CL.bitvectorType 1)
  szVal <- liftIO $ WI.bvLit sym (MC.memWidth mem) (fromIntegral sz)
  let ?ptrWidth = MC.memWidth mem
  let interval = IM.IntervalCO absAddr (absAddr + fromIntegral sz)
  case MMP.isReadonly (MC.segmentFlags seg) of
    True -> do
      (ptr, impl1) <- liftIO $ CL.doMalloc sym CL.GlobalAlloc CL.Immutable ("Read only memory at " ++ show addr) impl szVal CLD.noAlignment
      let alloc = Allocation { allocationPtr = ptr, allocationBase = absAddr }
      impl2 <- liftIO $ CL.storeConstRaw sym impl1 ptr ty CLD.noAlignment val
      return (impl2, IM.insert interval alloc ptrtable)
    False ->
      case mmc of
        ConcreteMutable -> do
          (ptr, impl1) <- liftIO $ CL.doMalloc sym CL.GlobalAlloc CL.Mutable ("Mutable (concrete) memory at " ++ show addr) impl szVal CLD.noAlignment
          let alloc = Allocation { allocationPtr = ptr, allocationBase = absAddr }
          impl2 <- liftIO $ CL.storeRaw sym impl1 ptr ty CLD.noAlignment val
          return (impl2, IM.insert interval alloc ptrtable)
        SymbolicMutable -> do
          let Right alloc_name = WI.userSymbol ("symbolicAllocBytes_" <> show addr)
          array <- liftIO $ WI.freshConstant sym alloc_name CT.knownRepr
          (ptr, impl1) <- liftIO $ CL.doMalloc sym CL.GlobalAlloc CL.Mutable ("Mutable (symbolic) memory at " ++ show addr) impl szVal CLD.noAlignment
          let alloc = Allocation { allocationPtr = ptr, allocationBase = absAddr }
          impl2 <- liftIO $ CL.doArrayStore sym impl1 ptr CLD.noAlignment array szVal
          return (impl2, IM.insert interval alloc ptrtable)

-- | The 'pleatM' function is 'foldM' with the arguments switched so
-- that the function is last.
pleatM :: (Monad m, F.Foldable t)
       => b
       -> t a
       -> (b -> a -> m b)
       -> m b
pleatM s l f = F.foldlM f s l


indexAllocations :: ( MC.MemWidth w
                    , Ord (WI.SymExpr sym WI.BaseNatType)
                    )
                 => IM.IntervalMap (MC.MemWord w) (Allocation sym w)
                 -> Map.Map (CS.RegValue sym CT.NatType) (Allocation sym w)
indexAllocations mappedMemory =
  F.foldl' indexAllocation Map.empty mappedMemory
  where
    indexAllocation m alloc =
      let (base, _) = CL.llvmPointerView (allocationPtr alloc)
      in Map.insert base alloc m

-- | Returns the allocation region (defined in the binary code) of a
-- base address if the address corresponds to one of the allocation
-- regions.
lookupAllocationBase :: (Ord (CS.RegValue sym CT.NatType))
                     => MemPtrTable sym w
                     -> (CS.RegValue sym CT.NatType)
                     -> Maybe (Allocation sym w)
lookupAllocationBase mpt baseAddr = Map.lookup baseAddr (allocationIndex mpt)


-- * mapRegionPointers

-- | Construct a translator for machine addresses into LLVM memory model pointers.
--
-- This translator is used by the symbolic simulator to resolve memory addresses.
mapRegionPointers :: ( MC.MemWidth w
                     , 16 <= w
                     , CB.IsSymInterface sym
                     )
                  => MemPtrTable sym w
                  -> MS.GlobalMap sym w
mapRegionPointers mpt = \sym mem regionNum offsetVal ->
  case WI.asNat regionNum of
    Just 0 -> mapBitvectorToLLVMPointer mpt sym mem offsetVal
    Just _ ->
      -- This is the case where the region number is concrete and non-zero,
      -- meaning that it is already an LLVM pointer
      return (Just (CL.LLVMPointer regionNum offsetVal))
    Nothing ->
      -- In this case, the region number is symbolic, so we need to be very
      -- careful to handle the possibility that it is zero (and thus must be
      -- conditionally mapped to one or all of our statically-allocated regions.
      mapSymbolicRegionPointer mpt sym mem regionNum offsetVal

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
                          -> IO (Maybe (CL.LLVMPtr sym w))
mapBitvectorToLLVMPointer mpt@(MemPtrTable im _) sym mem offsetVal =
  case WI.asUnsignedBV offsetVal of
    Just concreteOffset -> do
      -- This is the simplest case where the bitvector is concretely known.  We
      -- can map it to exactly one address.
      --
      -- FIXME: Assert that there is at most one element in here.  We could
      -- push the assertion to the creation site
      case IM.elems (IM.containing im (fromIntegral concreteOffset)) of
        [alloc] -> do
          -- Addresses inside of our allocations in the LLVM heap start at offset
          -- 0x0, so we have to subtract off the (logical) offset of the first
          -- value in the allocation to get the LLVM-level offset of the
          -- allocation we want.
          let wrep = WI.bvWidth offsetVal
          allocBase <- WI.bvLit sym wrep (MC.memWordToUnsigned (allocationBase alloc))
          allocationOffset <- WI.bvSub sym offsetVal allocBase
          let ?ptrWidth = wrep
          Just <$> CL.doPtrAddOffset sym (Just UB.laxConfig) mem (allocationPtr alloc) allocationOffset
        [] -> return Nothing
        _ -> error ("Overlapping allocations for pointer: " ++ show (WI.printSymExpr offsetVal))
    Nothing -> do
      -- This case is more complicated, as the bitvector value is at least
      -- partially symbolic.  This means that it could be in *any* of our
      -- statically-allocated region (in the MemPtrTable).
      --
      -- We still get our base assumption that the value cannot be on the stack
      -- or on the heap, as those cannot have a 0 region number (as they are
      -- always completely disjoint).
      --
      -- We will handle this by creating a mux tree that allows the pointer to
      -- be in *any* of our statically-allocated regions.
      Just <$> staticRegionMuxTree mpt sym mem offsetVal

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
                    -> IO (CL.LLVMPtr sym w)
staticRegionMuxTree (MemPtrTable im _) sym mem offsetVal = do
  let rep = WI.bvWidth offsetVal
  np <- CL.mkNullPointer sym rep
  F.foldlM addMuxForRegion np (IM.toList im)
  where
    handleCase f alloc start end greater less = do
      let rep = WI.bvWidth offsetVal
      startLit <- WI.bvLit sym rep (MC.memWordToUnsigned start)
      endLit <- WI.bvLit sym rep (MC.memWordToUnsigned end)
      gt <- greater sym offsetVal startLit
      lt <- less sym offsetVal endLit
      p <- WI.andPred sym gt lt
      allocBase <- WI.bvLit sym rep (MC.memWordToUnsigned (allocationBase alloc))
      allocationOffset <- WI.bvSub sym offsetVal allocBase
      let ?ptrWidth = rep
      thisPtr <- CL.doPtrAddOffset sym (Just UB.laxConfig) mem (allocationPtr alloc) allocationOffset
      CL.muxLLVMPtr sym p thisPtr f
    addMuxForRegion f (interval, alloc) = do
      case interval of
        IM.IntervalOC start end -> handleCase f alloc start end WI.bvUgt WI.bvUle
        IM.IntervalCO start end -> handleCase f alloc start end WI.bvUge WI.bvUlt
        IM.ClosedInterval start end -> handleCase f alloc start end WI.bvUge WI.bvUle
        IM.OpenInterval start end -> handleCase f alloc start end WI.bvUgt WI.bvUlt

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
                         -> IO (Maybe (CL.LLVMPtr sym w))
mapSymbolicRegionPointer mpt sym mem regionNum offsetVal = do
  zeroNat <- WI.natLit sym 0
  staticRegion <- staticRegionMuxTree mpt sym mem offsetVal
  isZeroRegion <- WI.natEq sym zeroNat regionNum
  let nonZeroPtr = CL.LLVMPointer regionNum offsetVal
  Just <$> CL.muxLLVMPtr sym isZeroRegion staticRegion nonZeroPtr
