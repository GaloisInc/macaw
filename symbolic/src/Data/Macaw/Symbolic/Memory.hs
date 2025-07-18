{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module provides a default configuration for the memory model that is
-- used during simulation. This implementation is generic and should be suitable
-- for most use cases, although it may not always perform well with binaries of
-- a certain size (see below for more details).
--
-- The documentation for 'MS.GlobalMap' describes the problem being solved in
-- detail. At a high level, we need to map bitvector values to pointers in the
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
-- by predicates in the program. The downside to this approach is that
-- initializing the initial state of the SMT array can be prohibitively
-- time-consuming for large binaries (i.e., megabytes or more in size). For
-- these binaries, you may want to consider the alternative memory model
-- configuration provided in the "Data.Macaw.Symbolic.Memory.Lazy" module.
--
-- Because the API in this module clashes with the API in
-- "Data.Macaw.Symbolic.Memory", it is recommended that you import these modules
-- with qualified imports.
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
  memModelConfig,
  MemPtrTable,
  MSMC.toCrucibleEndian,
  MSMC.fromCrucibleEndian,
  MSMC.GlobalMemoryHooks(..),
  MSMC.defaultGlobalMemoryHooks,
  newGlobalMemory,
  newGlobalMemoryWith,
  newMergedGlobalMemoryWith,
  MSMC.MemoryModelContents(..),
  MSMC.MacawProcessAssertion,
  MSMC.ignoreMacawAssertions,
  mkGlobalPointerValidityPred,
  mapRegionPointers
  ) where

import           GHC.TypeLits

import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.Functor.Identity ( Identity(Identity) )
import qualified Data.IntervalMap.Strict as IM

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.Types as CT
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI
import qualified What4.Symbol as WS

import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory.Common as MSMC

-- | The default memory model's configuration options:
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
-- * No attempt is made to to concretize pointers. That is, 'MS.resolvePointer'
--   will simply return its pointer argument unchanged.
--
-- * No special treatment is given to concrete reads from read-only memory.
--   That is, 'MS.concreteImmutableGlobalRead' always returns 'Nothing'.
--
-- * The memory model does not perform incremental updates before reads or
--   writes. That is, 'MS.lazilyPopulateGlobalMem' always returns its state
--   unchanged.
memModelConfig ::
     ( CB.IsSymBackend sym bak
     , w ~ MC.ArchAddrWidth arch
     , MC.MemWidth w
     , 16 <= w
     , CL.HasLLVMAnn sym
     , ?memOpts :: CL.MemOptions
     , MSMC.MacawProcessAssertion sym
     )
  => bak
  -> MemPtrTable sym w
  -> MS.MemModelConfig p sym arch CL.Mem
memModelConfig _ mpt =
  MS.MemModelConfig
    { MS.globalMemMap = mapRegionPointers mpt
    , MS.lookupFunctionHandle = MS.unsupportedFunctionCalls origin
    , MS.lookupSyscallHandle = MS.unsupportedSyscalls origin
    , MS.mkGlobalPointerValidityAssertion = mkGlobalPointerValidityPred mpt
    , MS.resolvePointer = pure
    , MS.concreteImmutableGlobalRead = \_ _ -> pure Nothing
    , MS.lazilyPopulateGlobalMem = \_ _ -> pure
    }
  where
    origin = "the default macaw-symbolic memory model"

-- | An index of all of the (statically) mapped memory in a program, suitable
-- for pointer translation
data MemPtrTable sym w =
  MemPtrTable { memPtrTable :: IM.IntervalMap (MC.MemWord w) CL.Mutability
              -- ^ The ranges of (static) allocations that are mapped
              , memPtr :: CL.LLVMPtr sym w
              -- ^ The pointer to the allocation backing all of memory
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
    , Foldable t'
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
newMergedGlobalMemoryWith hooks proxy bak endian mmc mems = do
  let sym = CB.backendGetSym bak
  let ?ptrWidth = MC.memWidthNatRepr @(MC.ArchAddrWidth arch)

  memImpl1 <- liftIO $ CL.emptyMem endian

  let allocName = WS.safeSymbol "globalMemoryBytes"
  symArray1 <- liftIO $ WI.freshConstant sym allocName CT.knownRepr
  sizeBV <- liftIO $ WI.maxUnsignedBV sym ?ptrWidth
  (ptr, memImpl2) <- liftIO $ CL.doMalloc bak CL.GlobalAlloc CL.Mutable
                         "Global memory for macaw-symbolic"
                         memImpl1 sizeBV CLD.noAlignment

  (symArray2, tbl) <- populateMemory proxy hooks bak mmc mems symArray1
  memImpl3 <- liftIO $ CL.doArrayStore bak memImpl2 ptr CLD.noAlignment symArray2 sizeBV
  let ptrTable = MemPtrTable { memPtrTable = tbl, memPtr = ptr }

  return (memImpl3, ptrTable)

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
                -> MSMC.MemoryModelContents
                -- ^ A configuration option controlling how mutable memory should be represented (concrete or symbolic)
                -> MC.Memory (MC.ArchAddrWidth arch)
                -- ^ The macaw memory
                -> m (CL.MemImpl sym, MemPtrTable sym (MC.ArchAddrWidth arch))
newGlobalMemory = newGlobalMemoryWith MSMC.defaultGlobalMemoryHooks

-- | Copy memory from the 'MC.Memory' into the LLVM memory model allocation as
-- directed by the 'MemoryModelContents' selection
populateMemory :: ( CB.IsSymBackend sym bak
                  , 16 <= MC.ArchAddrWidth arch
                  , MC.MemWidth (MC.ArchAddrWidth arch)
                  , KnownNat (MC.ArchAddrWidth arch)
                  , MonadIO m
                  , sym ~ WEB.ExprBuilder t st fs
                  , Foldable t'
                  )
               => proxy arch
               -- ^ A proxy to fix the architecture
               -> MSMC.GlobalMemoryHooks (MC.ArchAddrWidth arch)
               -- ^ Hooks controlling how memory should be initialized
               -> bak
               -- ^ The symbolic backend
               -> MSMC.MemoryModelContents
               -- ^ A flag to indicate how to populate the memory model based on the memory image
               -> t' (MC.Memory (MC.ArchAddrWidth arch))
               -- ^ The initial memory images for the binaries, which contain static data to populate the memory model
               -> WI.SymArray sym (CT.SingleCtx (WI.BaseBVType (MC.ArchAddrWidth arch))) (WI.BaseBVType 8)
               -> m ( WI.SymArray sym (CT.SingleCtx (WI.BaseBVType (MC.ArchAddrWidth arch))) (WI.BaseBVType 8)
                    , IM.IntervalMap (MC.MemWord (MC.ArchAddrWidth arch)) CL.Mutability
                    )
populateMemory proxy hooks bak mmc mems symArray0 =
  MSMC.pleatM (symArray0, IM.empty) mems $ \allocs0 mem ->
    MSMC.pleatM allocs0 (MC.memSegments mem) $ \allocs1 seg -> do
      MSMC.pleatM allocs1 (MC.relativeSegmentContents [seg]) $ \(symArray, allocs2) (addr, memChunk) -> do
        concreteBytes <- MSMC.populateMemChunkBytes bak hooks mem seg addr memChunk
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
                   -> MSMC.MemoryModelContents
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
            MSMC.ConcreteMutable ->
              ( CL.Mutable
              , True
              )
            MSMC.SymbolicMutable ->
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
        let absByteAddr = case MC.asAbsoluteAddr byteAddr of
                            Just absByteAddr' -> absByteAddr'
                            Nothing -> error $ "populateSegmentChunk: Could not make absolute address for: "
                                    ++ show byteAddr
        index_bv <- liftIO $ WI.bvLit sym (MC.memWidth mem) (fromIntegral absByteAddr)
        liftIO $ WI.arrayUpdate sym arr (Ctx.singleton index_bv) byte
-}

{-
      -- We don't use this method because it generates very large array update
      -- terms that, while what we want, crash yices (and make z3 and cvc4 eat
      -- huge amounts of memory)
      let addUpdate m (idx, byte) =
            let byteAddr = MC.incAddr (fromIntegral idx) addr
                absByteAddr = case MC.asAbsoluteAddr byteAddr of
                                Just absByteAddr' -> absByteAddr'
                                Nothing -> error $ "populateSegmentChunk: Could not make absolute address for: "
                                        ++ show byteAddr
                key = WI.BVIndexLit (MC.memWidth mem) (fromIntegral absByteAddr)
            in WUH.mapInsert (Ctx.singleton key) byte m
      let updates = F.foldl' addUpdate WUH.mapEmpty (zip [0..size - 1] bytes)
      symArray2 <- liftIO $ WI.arrayUpdateAtIdxLits sym updates symArray
-}

      bytesAssmp <-
        MSMC.memArrEqualityAssumption sym symArray (toAbsoluteAddr addr) bytes
      liftIO $ CB.addAssumption bak bytesAssmp
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
                               , MSMC.MacawProcessAssertion sym
                               )
                            => MemPtrTable sym w
                            -> MS.MkGlobalPointerValidityAssertion sym w
mkGlobalPointerValidityPred mpt =
  MSMC.mkGlobalPointerValidityPredCommon (memPtrTable mpt)

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
