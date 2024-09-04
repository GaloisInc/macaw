{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE MultiWayIf #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | This module defines common test harness code that can be used in each of the
-- architecture-specific backends.
--
-- The model is:
--
-- 1. Load an ELF file (returning the ELF) and run code discovery on it plus
--    any shared libraries that it depends on (returning a 'BinariesInfo').
--
-- 2. Provide the harness a list of discovered functions to simulate and try to
--    prove the result of (there is a helper for selecting tests whose name
--    begins with @test_@).
module Data.Macaw.Symbolic.Testing (
  runDiscovery,
  ResultExtractor(..),
  simulateAndVerify,
  SimulationResult(..),
  SATResult(..),
  MemModelPreset(..),
  describeMemModelPreset,
  toAddrSymMap,
  -- * Execution features
  SomeBackend(..),
  defaultExecFeatures,
  -- * @BinariesInfo@
  BinariesInfo(..),
  BinaryInfo(..),
  binaryInfoAt,
  countBinaries
  ) where

import qualified Control.Exception as X
import qualified Control.Lens as L
import           Control.Lens ( (&), (%~) )
import           Control.Monad ( when )
import           Control.Monad.Except ( runExceptT )
import qualified Data.Bits as Bits
import qualified Data.BitVector.Sized as BVS
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as EE
import qualified Data.Foldable as F
import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MEL
import qualified Data.Macaw.Memory.ElfLoader.DynamicDependencies as MELD
import qualified Data.Macaw.Memory.ElfLoader.PLTStubs as MELP
import qualified Data.Macaw.Memory.LoadCommon as MML
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory as MSM
import qualified Data.Macaw.Symbolic.Memory.Lazy as MSMLazy
import qualified Data.Macaw.Symbolic.Stack as MSS
import qualified Data.Macaw.Types as MT
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe, listToMaybe )
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Text as Text
import qualified Data.Text.Encoding as Text
import qualified Data.Text.Encoding.Error as Text
import qualified Data.Vector as V
import           Data.Word ( Word64 )
import           GHC.TypeNats ( type (<=) )
import qualified Lang.Crucible.Analysis.Postdom as CAP
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as CBO
import qualified Lang.Crucible.Backend.Prove as Prove
import qualified Lang.Crucible.CFG.Core as CCC
import qualified Lang.Crucible.CFG.Extension as CCE
import qualified Lang.Crucible.FunctionHandle as CFH
import qualified Lang.Crucible.LLVM.Intrinsics as CLI
import qualified Lang.Crucible.LLVM.MemModel as CLM
import qualified Lang.Crucible.Simulator as CS
import qualified Lang.Crucible.Simulator.GlobalState as CSG
import qualified Lang.Crucible.Simulator.PathSatisfiability as CSP
import qualified Lang.Crucible.Types as CT
import qualified Lang.Crucible.Utils.Seconds as Sec
import qualified Lang.Crucible.Utils.Timeout as CTO
import qualified System.FilePath as SF
import qualified System.IO as IO
import qualified What4.BaseTypes as WT
import qualified What4.Expr as WE
import qualified What4.FunctionName as WF
import qualified What4.Interface as WI
import qualified What4.LabeledPred as WL
import qualified What4.ProgramLoc as WPL
import qualified What4.Protocol.Online as WPO
import qualified What4.SatResult as WSR
import qualified What4.Solver as WS

data TestingException = ELFResolutionError String
  deriving (Show)

instance X.Exception TestingException

-- | Convert machine addresses into Crucible positions.
--
-- When possible, we map to the structured 'WPL.BinaryPos' type. However, some
-- 'MM.MemSegmentOff' cannot be mapped to an absolute position (e.g., some
-- addresses from shared libraries are in non-trivial segments). In those cases,
-- we map to the unstructured 'WPL.Others' with a sufficiently descriptive string.
posFn :: (MM.MemWidth w) => FilePath -> MM.MemSegmentOff w -> WPL.Position
posFn binaryName segOff =
  case MM.segoffAsAbsoluteAddr segOff of
    Just mw -> WPL.BinaryPos (Text.pack binaryName) (fromIntegral mw)
    Nothing -> WPL.OtherPos (Text.pack binaryName <> Text.pack ": " <> Text.pack (show segOff))

-- | Load an ELF file into a macaw 'MM.Memory' (and symbols)
loadELF :: MML.LoadOptions
        -> EE.ElfHeaderInfo w
        -> IO (MM.Memory w, [MEL.MemSymbol w])
loadELF loadOpts ehi = do
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
-- symbol attached to it, plus the program entry point) in a binary and the
-- shared libraries that it depends on. Return the resulting 'BinariesInfo'.
runDiscovery :: forall arch reloc w
              . ( MC.ArchAddrWidth arch ~ w
                , EE.RelocationWidth reloc ~ w
                , EE.IsRelocationType reloc
                , MM.MemWidth w
                )
             => EE.ElfHeaderInfo w
             -- ^ The ELF header info for the main binary
             -> FilePath
             -- ^ The main binary's file path
             -> (MM.Memory w -> [MEL.MemSymbol w] -> Map.Map (MM.MemSegmentOff w) BS.ByteString)
             -- ^ A function to turn discovered symbols into (address, name)
             -- mappings; the addresses are used as test entry points
             --
             -- A good default is 'toAddrSymMap'
             -> MAI.ArchitectureInfo arch
             -> MELP.PLTStubInfo reloc
             -- ^ Heuristics about how large PLT stubs should be.
             -> IO (BinariesInfo arch)
runDiscovery mainEHI mainPath toEntryPoints archInfo pltStubInfo = do
  -- First, perform code discovery on the main binary.
  let mainLoadOpts = MML.defaultLoadOptions
  (mainMem, mainNameAddrList) <- loadELF mainLoadOpts mainEHI
  let mainBinInfo  = mkBinaryInfo mainMem mainNameAddrList mainPath
  let mainDynFuns  = getDynamicFunAddrs mainLoadOpts mainEHI
  let mainPltStubs = mkPltStubMap mainLoadOpts mainEHI

  -- Next, load shared libraries.
  sos <- MELD.loadDynamicDependencies
           hdrMachine hdrClass
           -- We assume that all of the shared libraries live in the same
           -- directory as the main binary. See Note [Shared libraries]
           -- (Loading shared libraries).
           (SF.takeDirectory mainPath)
           mainEHI mainPath
  let sosV = V.fromList sos
  soTriples <-
    V.imapM (\idx (soEHI, soPath) ->
              do let soLoadOpts = sharedLibraryLoadOptions idx
                 (soMem, soNameAddrList) <- loadELF soLoadOpts soEHI
                 let soBinInfo  = mkBinaryInfo soMem soNameAddrList soPath
                 let soDynFuns  = getDynamicFunAddrs soLoadOpts soEHI
                 let soPltStubs = mkPltStubMap soLoadOpts soEHI
                 pure (soBinInfo, soDynFuns, soPltStubs))
            sosV
  let (soBinInfos, soDynFuns, soPltStubs) = V.unzip3 soTriples

  -- Finally, package everything up in a BinariesInfo
  let allDynFuns = fmap snd $
                   F.foldl'
                     (\m (funSym, (entry, addr)) ->
                       -- Load dynamic function symbols, prioritizing symbols
                       -- encountered earlier over later symbols. See
                       -- Note [Shared libraries] (Simulating PLT stubs in shared libraries).
                       addSymbolWithPriority funSym entry addr m)
                     (Map.fromList mainDynFuns) (concat soDynFuns)
  let allPltStubs = Map.unions (V.cons mainPltStubs soPltStubs)
  pure $ BinariesInfo
           { mainBinaryInfo = mainBinInfo
           , sharedLibraryInfos = soBinInfos
           , dynamicFunMap = allDynFuns
           , pltStubMap = allPltStubs
           }
  where
    hdr = EE.header mainEHI
    hdrMachine = EE.headerMachine hdr
    hdrClass = EE.headerClass hdr

    sharedLibraryLoadOptions :: Int -> MML.LoadOptions
    sharedLibraryLoadOptions idx =
      -- NB: Add 1 here to adhere to the binary indexing conventions laid out
      -- in Note [Shared libraries] (Address offsets for shared libraries).
      indexToLoadOptions (fromIntegral (idx + 1))

    mkBinaryInfo :: MM.Memory w -> [MEL.MemSymbol w] -> FilePath
                 -> BinaryInfo arch
    mkBinaryInfo mem nameAddrList path =
      let addrSymMap = toEntryPoints mem nameAddrList in
      let discState = MD.cfgFromAddrs archInfo mem addrSymMap
                                      (Map.keys addrSymMap) [] in
      BinaryInfo
        { binaryDiscState = discState
        , binaryPath = path
        }

    mkPltStubMap ::
         MML.LoadOptions
      -> EE.ElfHeaderInfo w
      -> Map.Map (MM.MemWord w) WF.FunctionName
    mkPltStubMap loadOpts ehi =
      fmap (\(entry, _) -> functionNameFromByteString (EE.steName entry))
           (MELP.pltStubSymbols pltStubInfo loadOpts ehi)

    getDynamicFunAddrs ::
         MML.LoadOptions
      -> EE.ElfHeaderInfo w
      -> [(WF.FunctionName, (EE.SymtabEntry BS.ByteString (EE.ElfWordType w), MM.MemWord w))]
    getDynamicFunAddrs loadOpts ehi =
      case EE.decodeHeaderDynsym ehi of
        Just (Right symtab) ->
            EE.elfClassInstances (EE.headerClass (EE.header ehi))
          $ V.toList
          $ V.map (\entry -> ( functionNameFromByteString $ EE.steName entry
                             , (entry, fromIntegral (EE.steValue entry) + fromIntegral offset)
                             ))
          $ V.filter isFuncSymbol
          $ EE.symtabEntries symtab
        _ -> []
      where
        offset = fromMaybe 0 $ MML.loadOffset loadOpts

data SATResult = Unsat | Sat | Unknown
  deriving (Eq, Show)

-- | Which preset memory model configuration to use during testing.
data MemModelPreset
  = DefaultMemModel
    -- ^ The default memory model in "Data.Macaw.Symbolic.Memory".
  | LazyMemModel
    -- ^ The lazy memory model in "Data.Macaw.Symbolic.Memory.Lazy".
  deriving (Eq, Show)

-- | A snappy description of a 'MemModelPreset', suitable for use in the output
-- of a test suite.
describeMemModelPreset :: MemModelPreset -> String
describeMemModelPreset DefaultMemModel = "Default memory model"
describeMemModelPreset LazyMemModel    = "Lazy memory model"

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
functionName dfi = maybe addrName functionNameFromByteString (MD.discoveredFunSymbol dfi)
  where
    addrName = WF.functionNameFromText (Text.pack (show (MD.discoveredFunAddr dfi)))

-- | Convert a 'BS.ByteString' to a 'WF.FunctionName'. This assumes that the
-- symbol name is UTF-8–encoded.
functionNameFromByteString :: BS.ByteString -> WF.FunctionName
functionNameFromByteString =
  WF.functionNameFromText . Text.decodeUtf8With Text.lenientDecode

proveGoals ::
  CB.IsSymBackend sym bak =>
  (sym ~ WE.ExprBuilder scope st fs) =>
  bak ->
  WS.SolverAdapter st ->
  IO ()
proveGoals bak goalSolver = do
  let sym = CB.backendGetSym bak
  let timeout = CTO.Timeout (Sec.secondsFromInt 5)
  let prover = Prove.offlineProver timeout sym WS.defaultLogData goalSolver
  let strat = Prove.ProofStrategy prover Prove.keepGoing
  let printer = Prove.ProofConsumer $ \goal res -> do
        let lp = CB.proofGoal goal
        case res of
          Prove.Proved {} -> return ()
          Prove.Disproved {} -> error ("Failed to prove goal: " ++ show (lp L.^. WL.labeledPredMsg))
          Prove.Unknown {} -> error ("Failed to prove goal: " ++ show (lp L.^. WL.labeledPredMsg))
  runExceptT (Prove.proveCurrentObligations bak strat printer) >>=
    \case
      Left CTO.TimedOut -> error "Timeout when proving goals!"
      Right () -> pure ()

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
--
-- In addition to symbolically executing the function to produce a Sat/Unsat
-- result, this function will attempt to verify all generate side conditions if
-- the name of the function being simulated begins with @test_and_verify_@ (as
-- opposed to just @test@).  This is necessary for testing aspects of the
-- semantics that involve the generated side conditions, rather than just the
-- final result.
simulateAndVerify :: forall arch sym bak ids w solver scope st fs
                   . ( CB.IsSymBackend sym bak
                     , CCE.IsSyntaxExtension (MS.MacawExt arch)
                     , MM.MemWidth (MC.ArchAddrWidth arch)
                     , w ~ MC.ArchAddrWidth arch
                     , 16 <= w
                     , MT.KnownNat w
                     , sym ~ WE.ExprBuilder scope st fs
                     , bak ~ CBO.OnlineBackend solver scope st fs
                     , WPO.OnlineSolver solver
                     , ?memOpts :: CLM.MemOptions
                     )
                  => WS.SolverAdapter st
                  -- ^ The solver adapter to use to discharge assertions
                  -> WS.LogData
                  -- ^ A logger to (optionally) record solver interaction (for the goal solver)
                  -> bak
                  -- ^ The symbolic backend
                  -> [CS.GenericExecutionFeature sym]
                  -- ^ Crucible execution features, see 'defaultExecFeatures' for a good initial selection
                  -> MAI.ArchitectureInfo arch
                  -- ^ The architecture info (only really used for endianness in this context)
                  -> MS.ArchVals arch
                  -- ^ Architecture-specific register state inspection and manipulation
                  -> BinariesInfo arch
                  -- ^ Information about the binaries to simulate. This includes
                  -- the initial contents of static memory and the discovered
                  -- functions.
                  -> MemModelPreset
                  -- ^ Which preset memory model configuration to use during simulation.
                  -> ResultExtractor sym arch
                  -- ^ A function to extract the return value of a function from its post-state
                  -> MD.DiscoveryFunInfo arch ids
                  -- ^ The function to simulate and verify
                  -> IO SimulationResult
simulateAndVerify goalSolver logger bak execFeatures archInfo archVals binfo mmPreset (ResultExtractor withResult) dfi =
  let sym = CB.backendGetSym bak in
  MS.withArchConstraints archVals $ do
    let funName = functionName dfi
    let mainInfo = mainBinaryInfo binfo
    halloc <- CFH.newHandleAllocator
    CCC.SomeCFG g <-
      MS.mkFunCFG (MS.archFunctions archVals) halloc funName (posFn (binaryPath mainInfo)) dfi

    let ?recordLLVMAnnotation = \_ _ _ -> return ()
    (memVar, stackPointer, execResult) <-
      simulateFunction binfo bak execFeatures archInfo archVals halloc mmPreset g
    case execResult of
      CS.TimeoutResult {} -> return SimulationTimeout
      CS.AbortedResult {} -> return SimulationAborted
      CS.FinishedResult _simCtx partialRes ->
        case partialRes of
          CS.PartialRes {} -> return SimulationPartial
          CS.TotalRes gp -> do
            when ("test_and_verify_" `Text.isPrefixOf` WF.functionName funName) $
              proveGoals bak goalSolver

            postMem <- case CSG.lookupGlobal memVar (gp L.^. CS.gpGlobals) of
                         Just postMem -> pure postMem
                         Nothing -> error $ "simulateAndVerify: Could not find global variable: "
                                         ++ Text.unpack (CS.globalName memVar)
            withResult (gp L.^. CS.gpValue) stackPointer postMem $ \resRepr val -> do
              -- The function is assumed to return a value that is intended to be
              -- True.  Try to prove that (by checking the negation for unsat)
              --
              -- The result is treated as true if it is not equal to zero
              zero <- WI.bvLit sym resRepr (BVS.mkBV resRepr 0)
              bv_val <- CLM.projectLLVM_bv bak val
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
simulateFunction :: forall arch sym bak w solver scope st fs ext blocks
                  . ( ext ~ MS.MacawExt arch
                    , CCE.IsSyntaxExtension ext
                    , CB.IsSymBackend sym bak
                    , CLM.HasLLVMAnn sym
                    , MS.SymArchConstraints arch
                    , w ~ MC.ArchAddrWidth arch
                    , 16 <= w
                    , sym ~ WE.ExprBuilder scope st fs
                    , bak ~ CBO.OnlineBackend solver scope st fs
                    , WPO.OnlineSolver solver
                    , ?memOpts :: CLM.MemOptions
                    )
                 => BinariesInfo arch
                 -> bak
                 -> [CS.GenericExecutionFeature sym]
                 -> MAI.ArchitectureInfo arch
                 -> MS.ArchVals arch
                 -> CFH.HandleAllocator
                 -> MemModelPreset
                 -> CCC.CFG ext blocks (Ctx.EmptyCtx Ctx.::> MS.ArchRegStruct arch) (MS.ArchRegStruct arch)
                 -> IO ( CS.GlobalVar CLM.Mem
                       , CLM.LLVMPtr sym w
                       , CS.ExecResult (MS.MacawLazySimulatorState sym w) sym ext (CS.RegEntry sym (MS.ArchRegStruct arch))
                       )
simulateFunction binfo bak execFeatures archInfo archVals halloc mmPreset g = do
  let sym = CB.backendGetSym bak
  let symArchFns = MS.archFunctions archVals
  let crucRegTypes = MS.crucArchRegTypes symArchFns
  let regsRepr = CT.StructRepr crucRegTypes
  let mainInfo = mainBinaryInfo binfo
  let soInfos = sharedLibraryInfos binfo
  let endianness = MSMLazy.toCrucibleEndian (MAI.archEndianness archInfo)
  let mems = V.map (MD.memory . binaryDiscState) (V.cons mainInfo soInfos)

  -- Initialize memory
  --
  -- This includes both global static memory (taken from the data segment
  -- initial contents) and a totally symbolic stack

  let ?ptrWidth = WI.knownRepr
  (initMem, mmConf) <-
    case mmPreset of
      DefaultMemModel -> do
        (initMem, memPtrTbl) <-
          MSM.newMergedGlobalMemoryWith populateRelocation (Proxy @arch) bak
            endianness MSM.ConcreteMutable mems
        let mmConf = (MSM.memModelConfig bak memPtrTbl)
                       { MS.lookupFunctionHandle = lookupFunction archVals binfo
                       , MS.lookupSyscallHandle = lookupSyscall
                       , MS.mkGlobalPointerValidityAssertion = validityCheck
                       }
        pure (initMem, mmConf)
      LazyMemModel -> do
        (initMem, memPtrTbl) <-
          MSMLazy.newMergedGlobalMemoryWith populateRelocation (Proxy @arch) bak
            endianness MSMLazy.ConcreteMutable mems
        let mmConf = (MSMLazy.memModelConfig bak memPtrTbl)
                       { MS.lookupFunctionHandle = lookupFunction archVals binfo
                       , MS.lookupSyscallHandle = lookupSyscall
                       , MS.mkGlobalPointerValidityAssertion = validityCheck
                       }
        pure (initMem, mmConf)

  -- Allocate a stack and insert it into memory
  --
  -- The stack allocation uses the SMT array backed memory model (rather than
  -- the Haskell-level memory model)
  let kib = 1024
  let mib = 1024 * kib
  stackSize <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr (2 * mib))
  (MSS.ArrayStack stackBasePtr _stackTopPtr _stackArrayStorage, mem1) <-
    MSS.createArrayStack bak initMem (MSS.ExtraStackSlots 0) stackSize

  -- Make initial registers, including setting up a stack pointer.
  --
  -- The stack pointer points to the middle of the stack allocation. This is a
  -- hack. We do this because each architecture has some expected stack layout
  -- (e.g., x86_64 expects a return address just above the stack pointer;
  -- PPC expects a "back chain"; and AArch32, PPC, and x86_64 all expect
  -- stack-spilled arguments above everything else). Setting the stack pointer
  -- to the middle of the allocation allows reads of fully symbolic data from
  -- above the stack pointer, and this seems to be good enough to make our tests
  -- pass.
  --
  -- The functions in the test-suite do not (and should not) rely on accessing
  -- data in their caller's stack frames, even though that wouldn't cause test
  -- failures with this setup.
  initialRegs <- MS.macawAssignToCrucM (mkInitialRegVal symArchFns sym) (MS.crucGenRegAssignment symArchFns)
  stackInitialOffset <- WI.bvLit sym WI.knownRepr (BVS.mkBV WI.knownRepr mib)
  sp <- CLM.ptrAdd sym WI.knownRepr stackBasePtr stackInitialOffset
  let initialRegsEntry = CS.RegEntry regsRepr initialRegs
  let regsWithStack = MS.updateReg archVals initialRegsEntry MC.sp_reg sp

  memVar <- CLM.mkMemVar "macaw-symbolic:test-harness:llvm_memory" halloc
  let lazySimSt = MS.emptyMacawLazySimulatorState
  let initGlobals = CSG.insertGlobal memVar mem1 CS.emptyGlobals
  let arguments = CS.RegMap (Ctx.singleton regsWithStack)
  let simAction = CS.runOverrideSim regsRepr (CS.regValue <$> CS.callCFG g arguments)

  let fnBindings = CFH.insertHandleMap (CCC.cfgHandle g) (CS.UseCFG g (CAP.postdomInfo g)) CFH.emptyHandleMap
  MS.withArchEval archVals sym $ \archEvalFn -> do
    let extImpl = MS.macawExtensions archEvalFn memVar mmConf
    let ctx = CS.initSimContext bak CLI.llvmIntrinsicTypes halloc IO.stdout (CS.FnBindings fnBindings) extImpl lazySimSt
    let s0 = CS.InitialState ctx initGlobals CS.defaultAbortHandler regsRepr simAction
    res <- CS.executeCrucible (fmap CS.genericToExecutionFeature execFeatures) s0
    return (memVar, sp, res)

-- | A wrapper around the symbolic backend that allows us to recover the online
-- constraints when they are available
--
-- The online constraints allow us to turn on path satisfiability checking
data SomeBackend sym where
  SomeOnlineBackend :: ( sym ~ WE.ExprBuilder scope st fs
                       , WPO.OnlineSolver solver
                       , CB.IsSymInterface sym
                       ) => CBO.OnlineBackend solver scope st fs -> SomeBackend sym
  SomeOfflineBackend :: sym -> SomeBackend sym

-- | A default set of execution features that are flexible enough to support a
-- wide range of tests.  If the backend provided supports online solving, the
-- execution features will include path satisfiability checking to allow simple
-- loops in test cases.
defaultExecFeatures :: SomeBackend sym -> IO [CS.GenericExecutionFeature sym]
defaultExecFeatures backend =
  case backend of
    SomeOfflineBackend {} -> return []
    SomeOnlineBackend bak -> do
      let sym = CB.backendGetSym bak
      pathSat <- CSP.pathSatisfiabilityFeature sym (CBO.considerSatisfiability bak)
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

resolveAbsoluteAddress
  :: (MM.MemWidth w)
  => MM.Memory w
  -> MM.MemWord w
  -> Maybe (MM.MemSegmentOff w)
resolveAbsoluteAddress mem addr =
  listToMaybe [ segOff
              | seg <- MM.memSegments mem
              , let region = MM.segmentBase seg
              , Just segOff <- return (MM.resolveRegionOff mem region addr)
              ]

addBinding
  :: CFH.FnHandle args ret
  -> CS.FnState p sym ext args ret
  -> CS.FunctionBindings p sym ext
  -> CS.FunctionBindings p sym ext
addBinding hdl fstate (CS.FnBindings binds) =
  CS.FnBindings (CFH.insertHandleMap hdl fstate binds)

lookupFunction
  :: forall p sym arch w
   . ( w ~ MC.ArchAddrWidth arch
     , MS.SymArchConstraints arch
     , CB.IsSymInterface sym
     )
  => MS.ArchVals arch
  -> BinariesInfo arch
  -> MS.LookupFunctionHandle p sym arch
lookupFunction archVals binariesInfo = MS.LookupFunctionHandle $ \s0 _memImpl regs -> do
  let regsEntry = CS.RegEntry regsRepr regs
  let (_, ptrOffset) = CLM.llvmPointerView (CS.regValue (MS.lookupReg archVals regsEntry MC.ip_reg))
  case WI.asBV ptrOffset of
    Just bvOff ->
      let funAddr = fromInteger $ BVS.asUnsigned bvOff in
      case Map.lookup funAddr (pltStubMap binariesInfo) of
        Just pltStubSym -> do
          (funAddrOff, binaryInfo) <- resolvePLTStub pltStubSym
          dispatchFunAddrOff s0 funAddrOff binaryInfo
        Nothing -> do
          (funAddrOff, binaryInfo) <- resolveFunAddrAndBin funAddr
          dispatchFunAddrOff s0 funAddrOff binaryInfo
    _ -> error ("Symbolic pointer offset in lookupFunction: " ++ show (WI.printSymExpr ptrOffset))
  where
    symArchFns = MS.archFunctions archVals
    crucRegTypes = MS.crucArchRegTypes symArchFns
    regsRepr = CT.StructRepr crucRegTypes

    -- Resolve the address that a PLT stub will jump to, also returning the
    -- binary that the address resides in.
    resolvePLTStub :: WF.FunctionName -> IO (MM.MemSegmentOff w, BinaryInfo arch)
    resolvePLTStub pltStubSym =
      case Map.lookup pltStubSym (dynamicFunMap binariesInfo) of
        Just funcAddr -> resolveFunAddrAndBin funcAddr
        Nothing -> error $
          "Missing implementation or override for shared library function: " ++
          show pltStubSym

    -- Resolve an address offset, also returning the binary that the address
    -- resides in.
    resolveFunAddrAndBin :: MM.MemWord w -> IO (MM.MemSegmentOff w, BinaryInfo arch)
    resolveFunAddrAndBin funAddr =
      case binaryInfoAt binariesInfo binIndex of
        Just binaryInfo ->
          case resolveAbsoluteAddress (MD.memory (binaryDiscState binaryInfo)) funAddr of
            Just funAddrOff -> pure (funAddrOff, binaryInfo)
            Nothing -> error $
              "Failed to resolve function address: " ++ show funAddr
        Nothing -> error $
          "Requested address " ++ show funAddr ++ " from binary with index " ++
          show binIndex ++ ", but only " ++ show (countBinaries binariesInfo) ++
          " binaries were discovered."
      where
        binIndex = fromInteger $ addressToIndex funAddr

    dispatchFunAddrOff ::
         forall args ret ext rtp blocks r ctx
       . ( args ~ (CT.EmptyCtx CT.::> CT.StructType (MS.MacawCrucibleRegTypes arch))
         , ret ~ CT.StructType (MS.MacawCrucibleRegTypes arch)
         , ext ~ MS.MacawExt arch
         )
      => CS.CrucibleState p sym ext rtp blocks r ctx
      -> MM.MemSegmentOff w
      -> BinaryInfo arch
      -> IO ( CFH.FnHandle args ret
            , CS.CrucibleState p sym ext rtp blocks r ctx
            )
    dispatchFunAddrOff s0 funAddrOff binaryInfo =
      case Map.lookup funAddrOff (binaryDiscState binaryInfo L.^. MD.funInfo) of
        Just (Some targetFn) -> do
          let funName = functionName targetFn
          halloc <- CFH.newHandleAllocator
          CCC.SomeCFG g <-
            MS.mkFunCFG symArchFns halloc funName (posFn (binaryPath binaryInfo)) targetFn
          hdl <- CFH.mkHandle' halloc funName (Ctx.singleton regsRepr) regsRepr
          let fstate = CS.UseCFG g (CAP.postdomInfo g)
          let s1 = s0 & CS.stateContext . CS.functionBindings %~ addBinding hdl fstate
          return (hdl, s1)
        Nothing -> error $
          "Could not find function address " ++ show funAddrOff ++ " in discovery info"

-- | The test harness does not currently support making system calls from test cases.
--
-- It could be modified to do so.
lookupSyscall :: MS.LookupSyscallHandle p sym arch
lookupSyscall = MS.unsupportedSyscalls "macaw-symbolic-tests"

-- | The test suite does not currently generate global pointer well-formedness
-- conditions (though it could be changed to do so).  This could become a
-- parameter.
validityCheck :: MS.MkGlobalPointerValidityAssertion sym w
validityCheck _ _ _ _ = return Nothing

-- | The test harness currently treats relocations as entirely symbolic data.
-- Most test cases will be unaffected by this, provided that they do not use
-- relocations in the test functions themselves.
-- See @Note [Shared libraries] (Dynamic relocations)@.
populateRelocation :: MSMLazy.GlobalMemoryHooks w
populateRelocation = MSMLazy.GlobalMemoryHooks
  { MSMLazy.populateRelocation = \bak _ _ _ reloc ->
      symbolicRelocation (CB.backendGetSym bak) reloc
  }
  where
    symbolicRelocation sym reloc =
      mapM (symbolicByte sym "reloc") [1 .. MM.relocationSize reloc]

    symbolicByte sym name idx = do
      let symbol = WI.safeSymbol $ name ++ "-byte" ++ show (idx-1)
      WI.freshConstant sym symbol WI.knownRepr

-- | Return true if this symbol table entry corresponds to a
-- globally defined symbol.
isGlobalSymbol :: EE.SymtabEntry nm w -> Bool
isGlobalSymbol e
  =  EE.steBind e `elem` [EE.STB_GLOBAL, EE.STB_WEAK] -- See Note [Shared libraries] (Weak symbols)
  && EE.steIndex e /= EE.SHN_UNDEF
  && EE.steIndex e <  EE.SHN_LORESERVE

-- | Return true if this symbol table entry corresponds to a
-- globally defined function.
isFuncSymbol :: Integral w => EE.SymtabEntry nm w -> Bool
isFuncSymbol e
  =  EE.steType e == EE.STT_FUNC
  && toInteger (EE.steValue e) /= 0
  && isGlobalSymbol e

-- | Add a new @symbol@ (which has been derived from a 'EE.SymtabEntry' in some
-- way) and associated @v@ value to a 'Map.Map'. If the 'Map.Map' already
-- contains that @symbol@, the conflict is resolved as follows:
--
-- 1. Global symbols are favored over weak symbols. See @Note [Shared libraries]
--    (Weak symbols)@. The only reason the 'Map.Map' includes a 'EE.SymtabEntry'
--    in its range is because we need to consult its 'EE.steBind' during this
--    step.
--
-- 2. Otherwise, favor the already-encountered @symbol@ over the new @symbol@.
--    This is what implements the lookup scope scheme described in
--    @Note [Dynamic lookup scope]@ in
--    "Data.Macaw.Memory.ElfLoader.DynamicDependencies".
addSymbolWithPriority ::
  Ord symbol =>
  symbol ->
  EE.SymtabEntry nm (EE.ElfWordType w) ->
  MM.MemWord w ->
  Map.Map symbol (EE.SymtabEntry nm (EE.ElfWordType w), MM.MemWord w) ->
  Map.Map symbol (EE.SymtabEntry nm (EE.ElfWordType w), MM.MemWord w)
addSymbolWithPriority newSym newSt newVal =
  Map.insertWith
    (\new@(newSte, _newVal) old@(oldSte, _oldVal) ->
      if -- Step (1)
         |  EE.steBind oldSte == EE.STB_GLOBAL
         ,  EE.steBind newSte == EE.STB_WEAK
         -> old

         |  EE.steBind newSte == EE.STB_GLOBAL
         ,  EE.steBind oldSte == EE.STB_WEAK
         -> new

         -- Step (2)
         |  otherwise
         -> old)
    newSym (newSt, newVal)

-- | All of the loaded binaries, along with information about the symbols in the
-- binaries.
data BinariesInfo arch = BinariesInfo
  { mainBinaryInfo :: BinaryInfo arch
    -- ^ The main binary.
  , sharedLibraryInfos :: V.Vector (BinaryInfo arch)
    -- ^ The shared libraries that the main binary depends on, either directly
    -- or indirectly.
  , dynamicFunMap :: Map.Map WF.FunctionName (MM.MemWord (MC.ArchAddrWidth arch))
    -- ^ A map of global, dynamic function symbol names to their corresponding
    -- function addresses. See @Note [Shared libraries] (Simulating PLT stubs in shared
    -- libraries)@.
  , pltStubMap :: Map.Map (MM.MemWord (MC.ArchAddrWidth arch)) WF.FunctionName
    -- ^ A map of PLT stub addresses to their corresponding function symbol
    -- names. See @Note [Shared libraries] (Simulating PLT stubs in shared
    -- libraries)@.
    --
    -- Note that the absolute address conventions that we use (see
    -- @Note [Shared libraries] (Address offsets for shared libraries)@ ensure
    -- that the addresses in shared libraries are always disjoint from each
    -- other, which ensures that there will never be clashes when inserting
    -- them into the map. If adopting a more sophisticated approach (e.g.,
    -- address-space layout randomization), this assumption will need to be
    -- revisited.
  }

-- | Information about an individual binary.
data BinaryInfo arch = BinaryInfo
  { binaryDiscState :: MD.DiscoveryState arch
    -- ^ The result of performing code discovery on the binary.
  , binaryPath :: FilePath
    -- ^ The file path to the binary.
  }

-- | Given an index (starting at zero), return the corresponding binary in the
-- 'BinariesInfo', adhering to the indexing conventions established in
-- @Note [Shared libraries] (Address offsets for shared libraries)@.
binaryInfoAt :: BinariesInfo arch -> Int -> Maybe (BinaryInfo arch)
binaryInfoAt binfo 0   = Just (mainBinaryInfo binfo)
binaryInfoAt binfo idx = sharedLibraryInfos binfo V.!? (idx - 1)

-- | Return how many binaries are included in the sum of the main binary and
-- the shared libraries in a 'BinariesInfo'.
countBinaries :: BinariesInfo arch -> Int
countBinaries binfo = 1 + V.length (sharedLibraryInfos binfo)

-- | Given an index value, constructs an 'MML.LoadOptions' for the appropriate
-- offset to load a shared object at.
-- See @Note [Shared libraries] (Address offsets for shared libraries)@.
indexToLoadOptions :: Word64 -> MML.LoadOptions
indexToLoadOptions index =
  MML.LoadOptions { MEL.loadOffset = Just $ loadOffset * index }

-- | Given an address offset, determine the index of the binary that defines
-- the address. Examples:
--
-- @
-- 'addressToLoadOffset' 0x00001000 = 0
-- 'addressToLoadOffset' 0x10001000 = 1
-- 'addressToLoadOffset' 0x10001110 = 1
-- 'addressToLoadOffset' 0x20001110 = 2
-- @
--
-- See @Note [Shared libraries] (Address offsets for shared libraries)@.
addressToIndex :: MM.MemWord w -> Integer
addressToIndex addr = MM.memWordToUnsigned addr `Bits.shiftR` 28
  -- NB: 28 is equal to log_2(0x10000000), i.e., the number of binary
  -- digits we must shift past to uncover the high bits.

-- | The address offset to use.
-- See @Note [Shared libraries] (Address offsets for shared libraries)@.
loadOffset :: Word64
loadOffset = 0x10000000

{-
Note [Shared libraries]
~~~~~~~~~~~~~~~~~~~~~~~
This module provides functional (but greatly simplified) means to simulate
binaries that dynamically link shared libraries. We make several assumptions
about how shared libraries work that are not true in general, but close enough
for our purposes. This Note describes all of these assumptions.

=====
== Address offsets for shared libraries
=====

When loading a binary with shared library dependencies, we must ensure that the
absolute addresses for each binary do not clash with each other. We accomplish
this by using the following conventions for address offsets when loading
binaries:

* Addresses in the main binary are loaded as-is.
* For shared libraries lib_1, lib_2, ..., lib_n, the addresses in lib_i are
  offset by `0x10000000 * i`. (See `indexToLoadOptions`.)

When resolving address in macaw, we must also go in the opposite direction.
That is, we must be able to take an address with an already-applied offset and
determine which binary it originally came from. To do so:

* The `addressToIndex` function masks off the low bits in the address to
  determine the index of the binary. For instance, given the address
  0x20001000, its high bits are 2, indicating that the address comes from the
  second shared library. If the index is 0, then the address comes from the
  main binary.
* A `BinariesInfo` value contains the main binary and a vector containing each
  shared library at an index suitable for use with the indexing conventions
  established above. To retrieve the appropriate Memory for an address offset,
  use the value computed by `addressToIndex` as an index into `binaryInfoAt`.

Be aware of the caveats to this approach to offsets:

* This load offset calculation is safe so long as all binaries are
  under 256MB.  It seems likely that something else in macaw would
  fail before binaries reach that size.

* On 32-bit architectures, index values of 16 or higher will cause
  the offset to reach inaccessible values.  Macaw throws an exception in
  this case.  If this occurs in practice we will need to reduce the offset
  multiplier to something smaller (the trade-off is that the maximum
  allowable library size will also decrease).

* This approach requires some care regarding PLT stubs, as they add a layer of
  indirection between PLT function addresses, which reside in one binary, and
  the addresses that they ultimately jump to, which reside in a different
  binary. (See Note [PLT stub names] in Data.Macaw.Memory.ElfLoader.PLTStubs.)
  For this reason, PLT stubs are handled in a special case in `lookupFunction`
  that bypasses the indexing mechanisms described above.

* The commentary above describes one particular load strategy for shared
  objects. In the future, we will want to be able to configure the load
  strategy so that we can model things like address-space layout randomization
  (ASLR). If we do this, we will need to update the code for resolving addresses
  accordingly.

=====
== Loading shared libraries
=====

The `runDiscovery` function is responsible for actually loading each shared
library, making sure to respect the indexing conventions established above.
See Note [Dynamic lookup scope] in Data.Macaw.Memory.ElfLoader.DynamicDependencies
for a description of the assumptions that are made when loading shared
libraries. One additional assumption that we make is that all of a binary's
shared libraries live in the same directory as the binary itself, which is fine
for testing purposes.

=====
== Simulating PLT stubs in shared libraries
=====

As described above, each shared library's absolute addresses are loaded at
different offsets so that they will not clash with each other during
simulation. But how does the simulator know when one binary calls into a
different shared library? This is where PLT stubs come into play.

When the simulator encounters a PLT stub in a binary, that indicates that it
must now simulate a function of the same name in a shared library.  The
`dynamicFunMap` field in a `BinariesInfo` value maps the names of global,
dynamic functions (which are the only functions that PLT stubs could reasonably
jump to) to their absolute addresses.  The simulator consults the
`dynamicFunMap` to determine which shared library to jump to and then proceeds
like normal. See `lookupFunction` for how this is implemented.

Constructing the `dynamicFunMap` is somewhat subtle, as it is possible for
multiple shared libraries to define global functions with the same name. If
this happens, then macaw uses the following approach to determine which
function symbol gets priority, as implemented in the `addSymbolWithPriority`
function:

1. Global symbols are favored over weak symbols. See the "Weak symbols" section
   for more details.

2. Otherwise, favor symbols that appear in earlier binaries over later ones,
   as described in the the lookup scheme in Note [Dynamic lookup scope] in
   Data.Macaw.Memory.ElfLoader.DynamicDependencies.

=====
== Weak symbols
=====

Weak symbols are like global symbols, except that a weak symbol is allowed to
be overridden by a global symbol of the same name. Libraries like libc use weak
symbols all over the place. For instance, libc might have a weak symbol named
setuid and a global symbol named __setuid at the same function address. A PLT
stub that jumps to setuid() will likely use the former symbol name, however, so
it's important for macaw to be aware of them.

Much of the time, if a weak symbol exists in a binary, then there is no
corresponding global symbol of the same name. This is because the linker
usually removes weak symbols of this sort, so by the time macaw-symbolic
simulates the binary, any potential name conflicts between weak and global
symbols have already been resolved. Still, it's difficult to state with
confidence that such a scenario could never happen. Just in case it does, we
manually resolve such naming conflicts (in `addSymbolWithPriority`) by favoring
global symbols over weak symbols in case of a name conflict.

=====
== Dynamic relocations
=====

For now, we do wish to handle the intricacies of dynamic relocations. We need
to do /something/ about relocations, however, since macaw-symbolic will need to
load them into the global address space. Our approach (as implemented in
`populateRelocation`) is to populate relocation regions of the address space
with symbolic bytes. As long as the test cases do not make critical use of
relocations, this is a reasonable choice.
-}
