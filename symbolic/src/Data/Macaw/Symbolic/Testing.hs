{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module defines common test harness code that can be used in each of the
-- architecture-specific backends
--
-- The model is:
--
-- 1. Load an ELF file and run code discovery on it (returning the ELF and a DiscoveryFunInfo)
--
-- 2. Provide the harness a list of discovered functions to simulate and try to
--    prove the result of (there is a helper for selecting tests whose name
--    begins with test_)
--
-- Note that tests invoked by this harness must not call other functions, as
-- function resolution is not set up.
module Data.Macaw.Symbolic.Testing (
  runDiscovery,
  ResultExtractor(..),
  simulateAndVerify,
  SimulationResult(..),
  SATResult(..),
  toAddrSymMap,
  -- * Execution features
  SomeBackend(..),
  defaultExecFeatures
  ) where

import qualified Control.Exception as X
import qualified Control.Lens as L
import qualified Control.Monad.ST as ST
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as EE
import qualified Data.Foldable as F
import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MEL
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory as MSM
import qualified Data.Macaw.Types as MT
import qualified Data.Map as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Encoding.Error as Text
import qualified Data.Traversable as T
import           GHC.TypeNats ( type (<=) )
import qualified Lang.Crucible.Analysis.Postdom as CAP
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.CFG.Extension as CCE
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.DataLayout as CLD
import qualified Lang.Crucible.LLVM.Intrinsics as CLI
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CSG
import qualified Lang.Crucible.Simulator.PathSatisfiability as CSP
import qualified Lang.Crucible.Types as CT
import qualified System.IO as IO
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WPL
import qualified What4.Protocol.Online as WPO
import qualified What4.SatResult as WSR
import qualified What4.Solver as WS
import qualified What4.Symbol as WSym

data TestingException = ELFResolutionError String
  deriving (Show)

instance X.Exception TestingException

nullDiscoveryLogger :: (Monad m) => a -> m ()
nullDiscoveryLogger _ = return ()

posFn :: (MM.MemWidth w) => MM.MemSegmentOff w -> WPL.Position
posFn = WPL.OtherPos . Text.pack . show

-- | Load an ELF file into a macaw 'MM.Memory' (and symbols)
loadELF :: EE.ElfHeaderInfo w
        -> IO (MM.Memory w, [MEL.MemSymbol w])
loadELF ehi = do
  let loadOpts = MEL.defaultLoadOptions
  case MEL.resolveElfContents loadOpts ehi of
    Left err -> X.throwIO (ELFResolutionError err)
    Right (warnings, mem, _mentry, nameAddrList) -> do
      F.forM_ warnings $ \w -> do
        IO.hPutStrLn IO.stderr w
      return (mem, nameAddrList)

-- | Convert a list of symbols into a mapping from entry point addresses to function names
--
-- Meant to be passed to 'runDiscovery' to compute (named) entry points
--
-- NOTE that the 'MM.Memory' is unused, but provided to make the API cleaner
-- (since some clients do need a 'MM.Memory', and 'runDiscovery' passes that as
-- an extra argument).
toAddrSymMap :: MM.Memory w
             -> [MEL.MemSymbol w]
             -> Map.Map (MEL.MemSegmentOff w) BS.ByteString
toAddrSymMap _mem nameAddrList =
  Map.fromList [ (MEL.memSymbolStart msym, MEL.memSymbolName msym)
               | msym <- nameAddrList
               ]

-- | Run code discovery over every function entry point (i.e., a function with a
-- symbol attached to it, plus the program entry point) and return the resulting
-- 'MD.DiscoveryFunInfo' for each.
runDiscovery :: (MC.ArchAddrWidth arch ~ w)
             => EE.ElfHeaderInfo w
             -> (MM.Memory w -> [MEL.MemSymbol w] -> Map.Map (MM.MemSegmentOff w) BS.ByteString)
             -- ^ A function to turn discovered symbols into (address, name)
             -- mappings; the addresses are used as test entry points
             --
             -- A good default is 'toAddrySymMap'
             -> MAI.ArchitectureInfo arch
             -> IO (MM.Memory w, [Some (MD.DiscoveryFunInfo arch)])
runDiscovery ehi toEntryPoints archInfo = do
  (mem, nameAddrList) <- loadELF ehi
  let addrSymMap = toEntryPoints mem nameAddrList
  let ds0 = MD.emptyDiscoveryState mem addrSymMap archInfo
  fns <- T.forM (Map.keys addrSymMap) $ \entryPoint -> do
    -- We are discovering each function in isolation for now, so we can throw
    -- away the updated discovery state.
    --
    -- NOTE: If we extend this to support function calls, we will probably want
    -- to just turn this into a fold/use the main discovery entry point.
    (_ds1, dfi) <- ST.stToIO (MD.analyzeFunction nullDiscoveryLogger entryPoint MD.UserRequest ds0)
    return dfi
  return (mem, fns)

data SATResult = Unsat | Sat | Unknown
  deriving (Eq, Show)

data SimulationResult = SimulationAborted
                      | SimulationTimeout
                      | SimulationPartial
                      | SimulationResult SATResult
                      deriving (Eq, Show)

-- | Allocate a fresh symbolic value for initial register states
mkInitialRegVal :: (CB.IsSymInterface sym, MT.HasRepr (MC.ArchReg arch) MT.TypeRepr)
                => MS.MacawSymbolicArchFunctions arch
                -> sym
                -> MC.ArchReg arch tp
                -> IO (CS.RegValue' sym (MS.ToCrucibleType tp))
mkInitialRegVal archFns sym r = do
  let regName = MS.crucGenArchRegName archFns r
  case MT.typeRepr r of
    MT.BoolTypeRepr ->
      CS.RV <$> WI.freshConstant sym regName WT.BaseBoolRepr
    MT.BVTypeRepr w -> do
      c <- WI.freshConstant sym regName (WT.BaseBVRepr w)
      ptr <- CLM.llvmPointer_bv sym c
      return (CS.RV ptr)
    MT.TupleTypeRepr PL.Nil -> return (CS.RV Ctx.Empty)
    MT.TupleTypeRepr {} -> error ("Tuple-typed registers are not supported in the macaw-symbolic test harness: " ++ show regName)
    MT.FloatTypeRepr {} -> error ("Float-typed registers are not supported in the macaw-symbolic test harness: " ++ show regName)
    MT.VecTypeRepr {} -> error ("Vector-typed registers are not supported in the macaw-symbolic test harness: " ++ show regName)

-- | Create a name for the given 'MD.DiscoveryFunInfo'
--
-- If the function has no name, just use its address
functionName :: (MM.MemWidth (MC.ArchAddrWidth arch)) => MD.DiscoveryFunInfo arch ids -> WF.FunctionName
functionName dfi = maybe addrName fromByteString (MD.discoveredFunSymbol dfi)
  where
    addrName = WF.functionNameFromText (Text.pack (show (MD.discoveredFunAddr dfi)))
    fromByteString = WF.functionNameFromText . Text.decodeUtf8With Text.lenientDecode

-- | Convert the given function into a Crucible CFG, symbolically execute it,
-- and treat the return value as an assertion to be verified.
--
-- The initial environment of the symbolic execution populates global memory
-- with the (concrete) contents of the data segment.  It provides fully symbolic
-- inputs in all registers (except as directed by architecture-specific code).
--
-- An initial stack will be allocated and the stack pointer location will be
-- populated with an appropriate pointer into that storage.  The initial stack
-- will have completely symbolic contents.
--
-- One of the arguments to this function selects the return value from the
-- simulator state.
--
-- In the API, recall that 'MS.MacawSymbolicArchFunctions' are used during
-- *translation* of programs into Crucible, while 'MS.MacawArchEvalFn' is used
-- during symbolic execution (to provide interpretations to
-- architecture-specific primitives).
simulateAndVerify :: forall arch sym ids w t st fs
                   . ( CB.IsSymInterface sym
                     , CCE.IsSyntaxExtension (MS.MacawExt arch)
                     , MM.MemWidth (MC.ArchAddrWidth arch)
                     , w ~ MC.ArchAddrWidth arch
                     , 16 <= w
                     , MT.KnownNat w
                     , sym ~ WE.ExprBuilder t st fs
                     )
                  => WS.SolverAdapter st
                  -- ^ The solver adapter to use to discharge assertions
                  -> WS.LogData
                  -- ^ A logger to (optionally) record solver interaction (for the goal solver)
                  -> sym
                  -- ^ The symbolic backend
                  -> [CS.GenericExecutionFeature sym]
                  -- ^ Crucible execution features, see 'defaultExecFeatures' for a good initial selection
                  -> MAI.ArchitectureInfo arch
                  -- ^ The architecture info (only really used for endianness in this context)
                  -> MS.ArchVals arch
                  -- ^ Architecture-specific register state inspection and manipulation
                  -> MM.Memory w
                  -- ^ The initial contents of static memory
                  -> ResultExtractor sym arch
                  -- ^ A function to extract the return value of a function from its post-state
                  -> MD.DiscoveryFunInfo arch ids
                  -- ^ The function to simulate and verify
                  -> IO SimulationResult
simulateAndVerify goalSolver logger sym execFeatures archInfo archVals mem (ResultExtractor withResult) dfi =
  MS.withArchConstraints archVals $ do
    let funName = functionName dfi
    halloc <- CFH.newHandleAllocator
    CCC.SomeCFG g <- MS.mkFunCFG (MS.archFunctions archVals) halloc funName posFn dfi

    let endianness = toCrucibleEndian (MAI.archEndianness archInfo)
    let ?recordLLVMAnnotation = \_ _ -> return ()
    (initMem, memPtrTbl) <- MSM.newGlobalMemory (Proxy @arch) sym endianness MSM.ConcreteMutable mem
    let globalMap = MSM.mapRegionPointers memPtrTbl
    (memVar, stackPointer, execResult) <- simulateFunction sym execFeatures archVals halloc initMem globalMap g
    case execResult of
      CS.TimeoutResult {} -> return SimulationTimeout
      CS.AbortedResult {} -> return SimulationAborted
      CS.FinishedResult _simCtx partialRes ->
        case partialRes of
          CS.PartialRes {} -> return SimulationPartial
          CS.TotalRes gp -> do
            let Just postMem = CSG.lookupGlobal memVar (gp L.^. CS.gpGlobals)
            withResult (gp L.^. CS.gpValue) stackPointer postMem $ \resRepr val -> do
              -- The function is assumed to return a value that is intended to be
              -- True.  Try to prove that (by checking the negation for unsat)
              --
              -- The result is treated as true if it is not equal to zero
              zero <- WI.bvLit sym resRepr (BVS.mkBV resRepr 0)
              bv_val <- CLM.projectLLVM_bv sym val
              notZero <- WI.bvNe sym bv_val zero
              goal <- WI.notPred sym notZero
              WS.solver_adapter_check_sat goalSolver sym logger [goal] $ \satRes ->
                case satRes of
                  WSR.Sat {} -> return (SimulationResult Sat)
                  WSR.Unsat {} -> return (SimulationResult Unsat)
                  WSR.Unknown -> return (SimulationResult Unknown)

-- | Set up the symbolic execution engine with initial states and execute
--
-- It returns:
--
-- 1. The global variable that holds the memory state (allowing for
--    inspecting the post-state, which is extracted from the 'CS.ExecResult')
--
-- 2. The stack pointer for the function
--
-- 3. The result of symbolic execution
--
-- Note that the provided 'CLM.MemImpl' is expected to have its global state
-- populated as desired.  The default loader populates it with concrete (and
-- mutable) values taken from the data segment of the binary (as well as the
-- immutable contents of the text segment).
simulateFunction :: ( ext ~ MS.MacawExt arch
                    , CCE.IsSyntaxExtension ext
                    , CB.IsSymInterface sym
                    , CLM.HasLLVMAnn sym
                    , MS.SymArchConstraints arch
                    , w ~ MC.ArchAddrWidth arch
                    , 16 <= w
                    )
                 => sym
                 -> [CS.GenericExecutionFeature sym]
                 -> MS.ArchVals arch
                 -> CFH.HandleAllocator
                 -> CLM.MemImpl sym
                 -> MS.GlobalMap sym CLM.Mem w
                 -> CCC.CFG ext blocks (Ctx.EmptyCtx Ctx.::> MS.ArchRegStruct arch) (MS.ArchRegStruct arch)
                 -> IO ( CS.GlobalVar CLM.Mem
                       , CLM.LLVMPtr sym w
                       , CS.ExecResult (MS.MacawSimulatorState sym) sym ext (CS.RegEntry sym (MS.ArchRegStruct arch))
                       )
simulateFunction sym execFeatures archVals halloc initMem globalMap g = do
  let symArchFns = MS.archFunctions archVals
  let crucRegTypes = MS.crucArchRegTypes symArchFns
  let regsRepr = CT.StructRepr crucRegTypes

  -- Initialize memory
  --
  -- This includes both global static memory (taken from the data segment
  -- initial contents) and a totally symbolic stack

  -- Allocate a stack and insert it into memory
  --
  -- The stack allocation uses the SMT array backed memory model (rather than
  -- the Haskell-level memory model)
  stackArrayStorage <- WI.freshConstant sym (WSym.safeSymbol "stack_array") WI.knownRepr
  stackSize <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr (2 * 1024 * 1024))
  let ?ptrWidth = WI.knownRepr
  (stackBasePtr, mem1) <- CLM.doMalloc sym CLM.StackAlloc CLM.Mutable "stack_alloc" initMem stackSize CLD.noAlignment
  mem2 <- CLM.doArrayStore sym mem1 stackBasePtr CLD.noAlignment stackArrayStorage stackSize

  -- Make initial registers, including setting up a stack pointer (which points
  -- into the middle of the stack allocation, to allow accesses into the caller
  -- frame if needed (though it generally should not be)
  initialRegs <- MS.macawAssignToCrucM (mkInitialRegVal symArchFns sym) (MS.crucGenRegAssignment symArchFns)
  stackInitialOffset <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr (1024 * 1024))
  sp <- CLM.ptrAdd sym WI.knownRepr stackBasePtr stackInitialOffset
  let initialRegsEntry = CS.RegEntry regsRepr initialRegs
  let regsWithStack = MS.updateReg archVals initialRegsEntry MC.sp_reg sp

  memVar <- CLM.mkMemVar "macaw-symbolic:test-harness:llvm_memory" halloc
  let initGlobals = CSG.insertGlobal memVar mem2 CS.emptyGlobals
  let arguments = CS.RegMap (Ctx.singleton regsWithStack)
  let simAction = CS.runOverrideSim regsRepr (CS.regValue <$> CS.callCFG g arguments)

  let fnBindings = CFH.insertHandleMap (CCC.cfgHandle g) (CS.UseCFG g (CAP.postdomInfo g)) CFH.emptyHandleMap
  MS.withArchEval archVals sym $ \archEvalFn -> do
    let extImpl = MS.macawExtensions archEvalFn memVar globalMap lookupFunction validityCheck
    let ctx = CS.initSimContext sym CLI.llvmIntrinsicTypes halloc IO.stdout (CS.FnBindings fnBindings) extImpl MS.MacawSimulatorState
    let s0 = CS.InitialState ctx initGlobals CS.defaultAbortHandler regsRepr simAction
    res <- CS.executeCrucible (fmap CS.genericToExecutionFeature execFeatures) s0
    return (memVar, sp, res)

-- | A wrapper around the symbolic backend that allows us to recover the online
-- constraints when they are available
--
-- The online constraints allow us to turn on path satisfiability checking
data SomeBackend sym where
  SomeOnlineBackend :: ( sym ~ CBO.OnlineBackend scope solver fs
                       , WPO.OnlineSolver solver
                       , CB.IsSymInterface sym
                       ) => sym -> SomeBackend sym
  SomeOfflineBackend :: sym -> SomeBackend sym

-- | A default set of execution features that are flexible enough to support a
-- wide range of tests.  If the backend provided supports online solving, the
-- execution features will include path satisfiability checking to allow simple
-- loops in test cases.
defaultExecFeatures :: SomeBackend sym -> IO [CS.GenericExecutionFeature sym]
defaultExecFeatures backend =
  case backend of
    SomeOfflineBackend {} -> return []
    SomeOnlineBackend sym -> do
      pathSat <- CSP.pathSatisfiabilityFeature sym (CBO.considerSatisfiability sym)
      return [pathSat]

-- | This type wraps up a function that takes the post-state of a symbolic
-- execution and extracts the return value from executing that function
--
-- The details are architecture specific.  Some architectures return values via
-- dedicated registers, while others return values on the stack.
--
-- This function takes the final register state and the post-state of memory,
-- allowing arbitrary access.
--
-- Note that the function that clients provide could return any arbitrary
-- post-state value (e.g., a distinguished memory location) - the rest of this
-- test harness is agnostic.
--
-- The function parameter is a continuation under which the caller (i.e., the
-- test harness) has access to the value provided by the user of the test harness.
data ResultExtractor sym arch where
  ResultExtractor :: (forall a
                       . CS.RegEntry sym (MS.ArchRegStruct arch)
                      -> CLM.LLVMPtr sym (MC.ArchAddrWidth arch)
                      -> CLM.MemImpl sym
                      -> (forall n . (1 <= n) => PN.NatRepr n -> CLM.LLVMPtr sym n -> IO a)
                      -> IO a)
                  -> ResultExtractor sym arch

-- | The test harness does not currently support calling functions from test cases.
--
-- It could be modified to do so.
lookupFunction :: MS.LookupFunctionHandle sym arch
lookupFunction = MS.LookupFunctionHandle $ \_s _mem _regs -> do
  error "Function calls are not supported in the macaw-symbolic test harness"

-- | The test suite does not currently generate global pointer well-formedness
-- conditions (though it could be changed to do so).  This could become a
-- parameter.
validityCheck :: MS.MkGlobalPointerValidityAssertion sym w
validityCheck _ _ _ _ = return Nothing

-- | Convert from macaw endianness to the LLVM memory model endianness
toCrucibleEndian :: MEL.Endianness -> CLD.EndianForm
toCrucibleEndian e =
  case e of
    MM.LittleEndian -> CLD.LittleEndian
    MM.BigEndian -> CLD.BigEndian
