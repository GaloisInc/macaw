{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
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
  -- * Memory Management
  MemPtrTable,
  toCrucibleEndian,
  fromCrucibleEndian,
  newGlobalMemory,
  GlobalMemoryHooks(..),
  defaultGlobalMemoryHooks,
  newGlobalMemoryWith,
  newMergedGlobalMemoryWith,
  MemoryModelContents(..),
  mkGlobalPointerValidityPred,
  mapRegionPointers
  ) where

import           GHC.TypeLits

import qualified Control.Lens as L
import           Control.Monad
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.BitVector.Sized as BV
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
import           Text.Printf ( printf )
import qualified What4.Expr.App as WEA
import qualified What4.Expr.BoolMap as BoolMap
import qualified What4.Expr.Builder as WEB
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
              , memRepr :: PN.NatRepr w
              -- ^ Pointer width representative
              }

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
    populateRelocation = \_ r -> return (error ("SymbolicRef SegmentRanges are not supported yet: " ++ show r))
    }

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
 => GlobalMemoryHooks (MC.ArchAddrWidth arch)
 -- ^ Hooks customizing the memory setup
 -> proxy arch
 -- ^ A proxy to fix the architecture
 -> bak
 -- ^ The symbolic backend used to construct terms
 -> CLD.EndianForm
 -- ^ The endianness of values in memory
 -> MemoryModelContents
 -- ^ A configuration option controlling how mutable memory should be represented (concrete or symbolic)
 -> MC.Memory (MC.ArchAddrWidth arch)
 -- ^ The macaw memory
 -> m (CL.MemImpl sym, MemPtrTable sym (MC.ArchAddrWidth arch))
newGlobalMemoryWith hooks proxy bak endian mmc mem =
  newMergedGlobalMemoryWith hooks proxy bak endian mmc [mem]

-- | A version of 'newGlobalMemoryWith' that takes a list of memories and
-- merges them into a flat addresses space.
newMergedGlobalMemoryWith
 :: ( 16 <= MC.ArchAddrWidth arch
    , MC.MemWidth (MC.ArchAddrWidth arch)
    , KnownNat (MC.ArchAddrWidth arch)
    , CB.IsSymBackend sym bak
    , CL.HasLLVMAnn sym
    , MonadIO m
    , sym ~ WEB.ExprBuilder t st fs
    , ?memOpts :: CL.MemOptions
    )
 => GlobalMemoryHooks (MC.ArchAddrWidth arch)
 -- ^ Hooks customizing the memory setup
 -> proxy arch
 -- ^ A proxy to fix the architecture
 -> bak
 -- ^ The symbolic backend used to construct terms
 -> CLD.EndianForm
 -- ^ The endianness of values in memory
 -> MemoryModelContents
 -- ^ A configuration option controlling how mutable memory should be represented (concrete or symbolic)
 -> [MC.Memory (MC.ArchAddrWidth arch)]
 -- ^ The macaw memories
 -> m (CL.MemImpl sym, MemPtrTable sym (MC.ArchAddrWidth arch))
newMergedGlobalMemoryWith hooks proxy bak endian mmc mems = do
  let sym = CB.backendGetSym bak

  let ?ptrWidth =
        case map MC.memWidth mems of
          [] -> error "Cannot build merged global memory from empty list"
          x : xs ->
            -- Check that all memories have the same pointer width
            if all (testNatEq x) xs
            then x
            else error "Provided macaw memories have different pointer widths"

  memImpl1 <- liftIO $ CL.emptyMem endian

  let allocName = WS.safeSymbol "globalMemoryBytes"
  symArray1 <- liftIO $ WI.freshConstant sym allocName CT.knownRepr
  sizeBV <- liftIO $ WI.maxUnsignedBV sym ?ptrWidth
  (ptr, memImpl2) <- liftIO $ CL.doMalloc bak CL.GlobalAlloc CL.Mutable
                         "Global memory for macaw-symbolic"
                         memImpl1 sizeBV CLD.noAlignment

  (symArray2, tbl) <- populateMemory proxy hooks bak mmc mems symArray1
  memImpl3 <- liftIO $ CL.doArrayStore bak memImpl2 ptr CLD.noAlignment symArray2 sizeBV
  let ptrTable = MemPtrTable { memPtrTable = tbl, memPtr = ptr, memRepr = ?ptrWidth }

  return (memImpl3, ptrTable)

  where
    -- | Test that two 'PN.NatRepr's are equal
    testNatEq :: PN.NatRepr m -> PN.NatRepr n -> Bool
    testNatEq x y =
      case PN.testNatCases x y of
        PN.NatCaseEQ -> True
        _ -> False

-- | Create a new LLVM memory model instance ('CL.MemImpl') and an index that
-- enables pointer translation ('MemPtrTable').  The contents of the
-- 'CL.MemImpl' are populated based on the 'MC.Memory' (macaw memory) passed in.
--
-- The statically-allocated memory in the 'MC.Memory' is represented by a single
-- symbolic LLVM memory model allocation, which is backed by an SMT array.
-- Read-only data is copied in concretely.  Mutable data can be copied in as
-- concrete mutable data or as symbolic data, depending on the needs of the
-- symbolic execution task (the behavior is controlled by the
-- 'MemoryModelContents' parameter).
--
-- Note that, since memory is represented using a single SMT array, large
-- portions of unmapped memory are included in the mapping.  Additionally, SMT
-- arrays do not have notions of mutable or immutable regions.  These notions
-- are enforced via the 'MS.MkGlobalPointerValidityPred', which encodes valid
-- uses of pointers.  See 'mkGlobalPointerValidityPred' for details.
--
-- Note that this default setup is not suitable for dynamically linked binaries
-- with relocations in the data section, as it will call 'error' if it
-- encounters one. To handle dynamically linked binaries, see 'newGlobalMemoryWith'.
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
                -> MemoryModelContents
                -- ^ A configuration option controlling how mutable memory should be represented (concrete or symbolic)
                -> MC.Memory (MC.ArchAddrWidth arch)
                -- ^ The macaw memory
                -> m (CL.MemImpl sym, MemPtrTable sym (MC.ArchAddrWidth arch))
newGlobalMemory = newGlobalMemoryWith defaultGlobalMemoryHooks

-- | Copy memory from the 'MC.Memory' into the LLVM memory model allocation as
-- directed by the 'MemoryModelContents' selection
populateMemory :: ( CB.IsSymBackend sym bak
                  , 16 <= MC.ArchAddrWidth arch
                  , MC.MemWidth (MC.ArchAddrWidth arch)
                  , KnownNat (MC.ArchAddrWidth arch)
                  , MonadIO m
                  , sym ~ WEB.ExprBuilder t st fs
                  )
               => proxy arch
               -- ^ A proxy to fix the architecture
               -> GlobalMemoryHooks (MC.ArchAddrWidth arch)
               -- ^ Hooks controlling how memory should be initialized
               -> bak
               -- ^ The symbolic backend
               -> MemoryModelContents
               -- ^ A flag to indicate how to populate the memory model based on the memory image
               -> [MC.Memory (MC.ArchAddrWidth arch)]
               -- ^ The initial memory image for the binary, which contains static data to populate the memory model
               -> WI.SymArray sym (CT.SingleCtx (WI.BaseBVType (MC.ArchAddrWidth arch))) (WI.BaseBVType 8)
               -> m ( WI.SymArray sym (CT.SingleCtx (WI.BaseBVType (MC.ArchAddrWidth arch))) (WI.BaseBVType 8)
                    , IM.IntervalMap (MC.MemWord (MC.ArchAddrWidth arch)) CL.Mutability
                    )
populateMemory proxy hooks bak mmc mems symArray0 =
  let sym = CB.backendGetSym bak in
  pleatM (symArray0, IM.empty) mems $ \allocs0 mem ->
    pleatM allocs0 (MC.memSegments mem) $ \allocs1 seg -> do
      pleatM allocs1 (MC.relativeSegmentContents [seg]) $ \(symArray, allocs2) (addr, memChunk) -> do
        concreteBytes <- case memChunk of
          MC.RelocationRegion reloc -> liftIO $ populateRelocation hooks bak reloc
          MC.BSSRegion sz ->
            liftIO $ replicate (fromIntegral sz) <$> WI.bvLit sym PN.knownNat (BV.zero PN.knownNat)
          MC.ByteRegion bytes ->
            liftIO $ mapM (WI.bvLit sym PN.knownNat . BV.word8) $ BS.unpack bytes
        populateSegmentChunk proxy bak mmc mem symArray seg addr concreteBytes allocs2

-- | If we want to treat the contents of this chunk of memory (the bytes at the
-- 'MemAddr') as concrete, assert that the bytes from the symbolic array backing
-- memory match concrete values.  Otherwise, leave bytes as totally symbolic.
--
-- Note that this is populating memory for *part* of a segment, and not the
-- entire segment.  This is because segments can be stored as chunks of concrete
-- values.  The address is the address of a chunk and not a segment.
populateSegmentChunk :: ( 16 <= w
                      , MC.MemWidth w
                      , KnownNat w
                      , CB.IsSymBackend sym bak
                      , MonadIO m
                      , MC.ArchAddrWidth arch ~ w
                      , sym ~ WEB.ExprBuilder t st fs
                      )
                   => proxy arch
                   -> bak
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
                   -> m ( WI.SymArray sym (CT.SingleCtx (WI.BaseBVType (MC.ArchAddrWidth arch))) (WI.BaseBVType 8)
                        , IM.IntervalMap (MC.MemWord w) CL.Mutability
                        )
populateSegmentChunk _ bak mmc mem symArray seg addr bytes ptrtable = do
  let sym = CB.backendGetSym bak
  let ?ptrWidth = MC.memWidth mem
  let abs_addr = toAbsoluteAddr addr
  let size = length bytes
  let interval = IM.IntervalOC abs_addr (abs_addr + fromIntegral size)
  let (mut_flag, conc_flag) =
        case MMP.isReadonly (MC.segmentFlags seg) of
          True ->
            ( CL.Immutable
            , True
            )
          False -> case mmc of
            ConcreteMutable ->
              ( CL.Mutable
              , True
              )
            SymbolicMutable ->
              ( CL.Mutable
              , False
              )

  -- When we are treating a piece of memory as having concrete initial values
  -- (e.g., for read-only memory) taken from the binary.
  --
  -- There are two major strategies for this: assert to the solver that array
  -- slots have known values or directly update the initial array.
  --
  -- We currently choose the former, as the latter has been crashing solvers.
  case conc_flag of
    False -> return (symArray, IM.insert interval mut_flag ptrtable)
    True -> do
{-
      -- We don't use this method because repeated applications of updateArray
      -- are *very* slow for some reason

      symArray2 <- pleatM symArray (zip [0.. size - 1] bytes) $ \arr (idx, byte) -> do
        let byteAddr = MC.incAddr (fromIntegral idx) addr
        -- FIXME: We can probably properly handle all of the different segments
        -- here pretty easily when required... but we will need one array per
        -- segment.
        let Just absByteAddr = MC.asAbsoluteAddr byteAddr
        index_bv <- liftIO $ WI.bvLit sym (MC.memWidth mem) (fromIntegral absByteAddr)
        liftIO $ WI.arrayUpdate sym arr (Ctx.singleton index_bv) byte
-}

{-
      -- We don't use this method because it generates very large array update
      -- terms that, while what we want, crash yices (and make z3 and cvc4 eat
      -- huge amounts of memory)

      let addUpdate m (idx, byte) =
            let byteAddr = MC.incAddr (fromIntegral idx) addr
                Just absByteAddr = MC.asAbsoluteAddr byteAddr
                key = WI.BVIndexLit (MC.memWidth mem) (fromIntegral absByteAddr)
            in WUH.mapInsert (Ctx.singleton key) byte m
      let updates = F.foldl' addUpdate WUH.mapEmpty (zip [0..size - 1] bytes)
      symArray2 <- liftIO $ WI.arrayUpdateAtIdxLits sym updates symArray
-}

      -- We used to assert the equality of each byte separately.  This ended up
      -- being very slow for large binaries, as it synchronizes the pipe to the
      -- solver after each assertion. Instead, we now encode all of the initial
      -- values as equalities and generate a large conjunction that asserts them
      -- all at once.
      --
      -- The roundabout encoding below (using the low-level 'WEB.sbMakeExpr'
      -- API) is used because the natural encoding (using 'WI.andPred') attempts
      -- to apply an optimization called absorbtion (which attempts to discard
      -- redundant conjuncts). That optimization is quadratic in cost, which
      -- makes this encoding intractably expensive for large terms.  By using
      -- 'WEB.sbMakeExpr', we avoid that optimization (which will never fire for
      -- this term anyway, as there are no redundant conjuncts).
      initVals <- pleatM [] (zip [0.. size - 1] bytes) $ \bmvals (idx, byte) -> do
        let byteAddr = MC.incAddr (fromIntegral idx) addr
        let absByteAddr = toAbsoluteAddr byteAddr
        index_bv <- liftIO $ WI.bvLit sym (MC.memWidth mem) (BV.mkBV (MC.memWidth mem) (toInteger absByteAddr))
        eq_pred <- liftIO $ WI.bvEq sym byte =<< WI.arrayLookup sym symArray (Ctx.singleton index_bv)
        return (eq_pred : bmvals)
      let desc = printf "Bytes@[addr=%s,nbytes=%s]" (show addr) (show bytes)
      prog_loc <- liftIO $ WI.getCurrentProgramLoc sym
      byteEqualityAssertion <- liftIO $ WEB.sbMakeExpr sym (WEA.ConjPred (BoolMap.fromVars [(e, BoolMap.Positive) | e <- initVals]))
      liftIO $ CB.addAssumption bak (CB.GenericAssumption prog_loc desc byteEqualityAssertion)
      let symArray2 = symArray

      return (symArray2, IM.insert interval mut_flag ptrtable)

  where
    toAbsoluteAddr a =
      let segOff =
            case MC.resolveRegionOff mem (MC.addrBase a) (MC.addrOffset a) of
              Just offset -> offset
              Nothing -> error $ "Could not find segment offset for the region "
                              ++ show a
      in
      MC.segmentOffset seg + MC.segoffOffset segOff

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
mkGlobalPointerValidityPred :: ( CB.IsSymInterface sym
                               , MC.MemWidth w
                               )
                            => MemPtrTable sym w
                            -> MS.MkGlobalPointerValidityAssertion sym w
mkGlobalPointerValidityPred mpt = \sym puse mcond ptr -> do
  -- If this is a write, the pointer cannot be in an immutable range (so just
  -- return False for the predicate on that range).
  --
  -- Otherwise, the pointer is allowed to be between the lo/hi range
  let inMappedRange off (range, mut)
        | MS.pointerUseTag puse == MS.PointerWrite && mut == CL.Immutable = return (WI.falsePred sym)
        | otherwise =
          case range of
            IM.IntervalCO lo hi -> do
              let w = memRepr mpt
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUlt sym lobv off
              hib <- WI.bvUle sym off hibv
              WI.andPred sym lob hib
            IM.ClosedInterval lo hi -> do
              let w = memRepr mpt
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUlt sym lobv off
              hib <- WI.bvUlt sym off hibv
              WI.andPred sym lob hib
            IM.OpenInterval lo hi -> do
              let w = memRepr mpt
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUle sym lobv off
              hib <- WI.bvUle sym off hibv
              WI.andPred sym lob hib
            IM.IntervalOC lo hi -> do
              let w = memRepr mpt
              lobv <- WI.bvLit sym w (BV.mkBV w (toInteger lo))
              hibv <- WI.bvLit sym w (BV.mkBV w (toInteger hi))
              lob <- WI.bvUle sym lobv off
              hib <- WI.bvUlt sym off hibv
              WI.andPred sym lob hib

  let mkPred off = do
        ps <- mapM (inMappedRange off) (IM.toList (memPtrTable mpt))
        ps' <- WI.orOneOf sym (L.folded . id) ps
        -- Add the condition from a conditional write
        WI.itePred sym (maybe (WI.truePred sym) CS.regValue mcond) ps' (WI.truePred sym)


  let ptrVal = CS.regValue ptr
  let (ptrBase, ptrOff) = CL.llvmPointerView ptrVal
  case WI.asNat ptrBase of
    Just 0 -> do
      p <- mkPred ptrOff
      let msg = printf "%s outside of static memory range (known BlockID 0): %s" (show (MS.pointerUseTag puse)) (show (WI.printSymExpr ptrOff))
      let loc = MS.pointerUseLocation puse
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
      let msg = printf "%s outside of static memory range (unknown BlockID): %s" (show (MS.pointerUseTag puse)) (show (WI.printSymExpr ptrOff))
      let loc = MS.pointerUseLocation puse
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
                  -> MS.GlobalMap sym CL.Mem w
mapRegionPointers mpt = MS.GlobalMap $ \bak mem regionNum offsetVal ->
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
