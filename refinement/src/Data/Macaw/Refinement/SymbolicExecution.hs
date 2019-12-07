{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Refinement.SymbolicExecution
  ( RefinementContext(..)
  , defaultRefinementContext
  , smtSolveTransfer
  , IPModels(..)
  , isSpurious
  , ipModels
  )
where

import qualified Control.Lens as L
import           Control.Lens ( (^.) )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import           Data.Bits ( (.|.) )
import qualified Data.Foldable as F
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.AbsDomain.AbsState as MAA
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory as MS
import           Data.Maybe ( mapMaybe )
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import           Data.Proxy ( Proxy(..) )
import           GHC.TypeNats
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Simple as CBS
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.LLVM.DataLayout as LLVM
import qualified Lang.Crucible.LLVM.Intrinsics as LLVM
import qualified Lang.Crucible.LLVM.MemModel as LLVM
import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified System.IO as IO
import qualified What4.Concrete as W
import qualified What4.Expr.GroundEval as W
import qualified What4.Interface as W
import qualified What4.ProgramLoc as W
import qualified What4.Protocol.Online as W
import qualified What4.SatResult as W
import qualified What4.BaseTypes as WT
import qualified What4.ProblemFeatures as WPF
import qualified What4.LabeledPred as WLP

import qualified What4.Expr as WE
import Text.Printf ( printf )
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified System.IO as IO

data RefinementContext sym arch = RefinementContext
  { symbolicBackend :: sym
  , archVals :: MS.ArchVals arch
  , handleAllocator :: C.HandleAllocator
  , extensionImpl :: C.ExtensionImpl (MS.MacawSimulatorState sym) sym (MS.MacawExt arch)
  , memVar :: C.GlobalVar LLVM.Mem
  , mem :: LLVM.MemImpl sym
  -- ^ The base memory of the executable.  Note that this includes static data
  -- copied from the binary.
  , memPtrTable :: MS.MemPtrTable sym (M.ArchAddrWidth arch)
  , globalMappingFn :: MS.GlobalMap sym (M.ArchAddrWidth arch)
  , executableSegments :: [MM.MemSegment (M.ArchAddrWidth arch)]
  , memWidthRepr :: PN.NatRepr (M.ArchAddrWidth arch)
  }

-- | Given a solver backend and binary, create a 'RefinementContext' that has
-- all of the necessary bits to symbolically simulate machine code and query the
-- SMT solver for models of the IP
defaultRefinementContext
  :: forall arch bin sym
   . ( MS.SymArchConstraints arch
     , 16 <= M.ArchAddrWidth arch
     , CB.IsSymInterface sym
     , Ord (W.SymExpr sym WT.BaseNatType)
     )
  => sym
  -> MBL.LoadedBinary arch bin
  -> IO (RefinementContext sym arch)
defaultRefinementContext sym loaded_binary = do
  handle_alloc <- C.newHandleAllocator
  case MS.archVals (Proxy @arch) of
    Just arch_vals -> do

      mem_var <- LLVM.mkMemVar handle_alloc

      (mem0, mem_ptr_table) <- MS.newGlobalMemory
        (Proxy @arch)
        sym
        (MS.toCrucibleEndian $ MBL.memoryEndianness loaded_binary)
        MS.ConcreteMutable
        (MBL.memoryImage loaded_binary)

      let ?ptrWidth = W.knownNat
      let global_mapping_fn = \sym' mem' base off -> do
            flat_mem_ptr <- LLVM.mkNullPointer sym' ?ptrWidth
            MS.mapRegionPointers
              mem_ptr_table
              flat_mem_ptr
              sym'
              mem'
              base
              off

      let isExecutable = MMP.isExecutable . MM.segmentFlags
      let execSegs = filter isExecutable (MM.memSegments (MBL.memoryImage loaded_binary))

      MS.withArchEval arch_vals sym $ \arch_eval_fns -> do
        let ext_impl = MS.macawExtensions
              arch_eval_fns
              mem_var
              global_mapping_fn
              (MS.LookupFunctionHandle $ \_ _ _ -> undefined)

        return $ RefinementContext
          { symbolicBackend = sym
          , archVals = arch_vals
          , handleAllocator = handle_alloc
          , extensionImpl = ext_impl
          , memVar = mem_var
          , mem = mem0
          , memPtrTable = mem_ptr_table
          , globalMappingFn = global_mapping_fn
          , executableSegments = execSegs
          , memWidthRepr = MM.memWidth (MBL.memoryImage loaded_binary)
          }
    Nothing -> fail $ "unsupported architecture"

-- | A data type to represent the models we get back from the solver
--
-- This lets us distinguish between no models and too many models (exceeding the
-- number requested, probably indicating that they are spurious)
data IPModels a = NoModels
                | Models [a]
                | SpuriousModels

-- | Returns all models (unless there is a spurious result)
ipModels :: IPModels a -> Maybe [a]
ipModels m =
  case m of
    NoModels -> Just []
    Models ms -> Just ms
    SpuriousModels -> Nothing

isSpurious :: IPModels a -> Bool
isSpurious m =
  case m of
    SpuriousModels -> True
    NoModels -> False
    Models {} -> False

smtSolveTransfer
  :: forall arch t solver fs m sym ids proxy
   . ( MS.SymArchConstraints arch
     , 16 <= M.ArchAddrWidth arch
     , CB.IsSymInterface sym
     , W.OnlineSolver t solver
     , MonadIO m
     , sym ~ CBS.SimpleBackend t fs
     )
  => proxy solver
  -> RefinementContext sym arch
  -> M.DiscoveryState arch
  -> [M.ParsedBlock arch ids]
  -> m (IPModels (M.ArchSegmentOff arch))
smtSolveTransfer _ ctx discovery_state blocks = do

  -- FIXME: Maintain a Path data type that ensures that the list is non-empty (i.e., get rid of head)
  let entryBlock = head blocks
  let posFn = W.BinaryPos "" . maybe 0 fromIntegral . M.segoffAsAbsoluteAddr
  some_cfg <- liftIO $ MS.mkBlockPathCFG
    (MS.archFunctions (archVals ctx))
    (handleAllocator ctx)
    posFn
    blocks

  F.forM_ blocks $ \pb -> liftIO $ do
    printf "Block %s\n" (show (M.pblockAddr pb))
    putStrLn (show (PP.pretty pb))

  case some_cfg of
    C.SomeCFG cfg -> do
      let executionFeatures = []
      initialState <- initializeSimulator ctx cfg entryBlock

      let sym = symbolicBackend ctx
      assumptions <- F.toList . fmap (^. WLP.labeledPred) <$> liftIO (CB.collectAssumptions sym)

      -- Symbolically execute the relevant code in a fresh assumption
      -- environment so that we can avoid polluting the global solver state
      exec_res <- liftIO $ inFreshAssumptionFrame sym $ do
        C.executeCrucible executionFeatures initialState

      case exec_res of
        C.FinishedResult _ res -> do
          let res_regs = res ^. C.partialValue . C.gpValue
          case C.regValue $ (MS.lookupReg (archVals ctx)) res_regs M.ip_reg of
            LLVM.LLVMPointer res_ip_base res_ip_off -> do
              let features = WPF.useBitvectors .|. WPF.useSymbolicArrays .|. WPF.useStructs -- .|. WPF.useNonlinearArithmetic
              let hdl = Nothing
              solverProc :: W.SolverProcess t solver
                         <- liftIO $ W.startSolverProcess features hdl sym
              models <- extractIPModels ctx solverProc assumptions discovery_state res_ip_base res_ip_off
              _ <- liftIO $ W.shutdownSolverProcess solverProc
              return models
        C.AbortedResult _ aborted_res -> case aborted_res of
          C.AbortedExec reason _ ->
            fail ("simulation abort: " ++ show (CB.ppAbortExecReason reason))
          C.AbortedExit code ->
            fail ("simulation halt: " ++ show code)
          C.AbortedBranch{} ->
            fail "simulation abort branch"
        C.TimeoutResult{} -> fail "simulation timeout"

-- | Generate an initial register state
--
-- It includes:
--
-- * A fixed IP
-- * A stack pointer (passed as an argument)
-- * Any fixed register values learned through abstract interpretation
initialRegisterState :: forall arch sym m ids
                      . ( MS.SymArchConstraints arch
                        , CB.IsSymInterface sym
                        , MonadIO m
                        , Show (W.SymExpr sym WT.BaseNatType)
                        , Show (W.SymExpr sym (WT.BaseBVType (M.ArchAddrWidth arch)))
                        )
                     => RefinementContext sym arch
                     -> LLVM.MemImpl sym
                     -- ^ The memory state to start from
                     -> M.ParsedBlock arch ids
                     -- ^ The entry block of the path
                     -> C.RegValue sym (LLVM.LLVMPointerType (M.ArchAddrWidth arch))
                     -- ^ The stack pointer to use
                     -> m (C.RegMap sym (MS.MacawFunctionArgs arch))
initialRegisterState ctx memory entryBlock spVal = do
  let sym = symbolicBackend ctx
  let arch_vals = archVals ctx

  -- Build an IP value to populate the initial register state with
  let entryAddr = M.segoffAddr (M.pblockAddr entryBlock)
  ip_base <- liftIO $ W.natLit sym (fromIntegral (M.addrBase entryAddr))
  ip_off <- liftIO $ W.bvLit sym W.knownNat (M.memWordToUnsigned (M.addrOffset entryAddr))
  mip <- liftIO $ globalMappingFn ctx sym memory ip_base ip_off
  entryIPVal <- case mip of
    Nothing -> error ("IP is not mapped: " ++ show (ip_base, ip_off))
    Just ip -> return ip

  liftIO $ printf "Entry initial state"
  liftIO $ print (M.blockAbstractState entryBlock)

  let reg_types = MS.crucArchRegTypes (MS.archFunctions arch_vals)
  reg_vals <- Ctx.traverseWithIndex (freshSymVar sym "reg") reg_types
  let reg_struct0 = C.RegEntry (C.StructRepr reg_types) reg_vals
  let reg_struct1 = MS.updateReg arch_vals reg_struct0 M.ip_reg entryIPVal
  let reg_struct2 = MS.updateReg arch_vals reg_struct1 M.sp_reg spVal

  let absRegs = M.blockAbstractState entryBlock ^. MAA.absRegState
  reg_struct <- MapF.foldlMWithKey (addKnownRegValue ctx memory) reg_struct2 (M.regStateMap absRegs)

  return $ C.RegMap $ Ctx.singleton reg_struct

-- | If the abstract value is actually completely known, add it concretely to
-- the register state.
--
-- NOTE: This function could probably be extended to support non-singleton
-- finsets by generating mux trees over all of the possible values (with fresh
-- variables as predicates).
addKnownRegValue :: forall arch sym m tp w
                  . ( MS.SymArchConstraints arch
                    , CB.IsSymInterface sym
                    , MonadIO m
                    )
                 => RefinementContext sym arch
                 -> LLVM.MemImpl sym
                 -> C.RegEntry sym (MS.ArchRegStruct arch)
                 -> M.ArchReg arch tp
                 -> MAA.AbsValue w tp
                 -> m (C.RegEntry sym (MS.ArchRegStruct arch))
addKnownRegValue ctx memory regsStruct reg val =
  case val of
    MAA.FinSet bvs
      | [singleBV] <- F.toList bvs -> do
          let sym = symbolicBackend ctx
          base <- liftIO $ W.natLit sym 0
          off <- liftIO $ W.bvLit sym W.knownNat singleBV
          mptr <- liftIO $ globalMappingFn ctx sym memory base off
          case mptr of
            Nothing -> do
              liftIO $ putStrLn "Not a pointer (translation failed)"
              ptr <- liftIO $ LLVM.llvmPointer_bv sym off
              addPtrVal ptr
            Just ptr -> addPtrVal ptr
    _ -> return regsStruct
  where
    addPtrVal :: LLVM.LLVMPtr sym (M.ArchAddrWidth arch) -> m (C.RegEntry sym (MS.ArchRegStruct arch))
    addPtrVal ptr = do
      let oldEntry = MS.lookupReg (archVals ctx) regsStruct reg
      let nr = W.knownNat @(M.ArchAddrWidth arch)
      case testEquality (C.regType oldEntry) (LLVM.LLVMPointerRepr nr) of
        Just Refl -> do
          liftIO $ printf "Populating register %s with %s\n" (show (M.prettyF reg)) (show (LLVM.ppPtr ptr))
          return (MS.updateReg (archVals ctx) regsStruct reg ptr)
        Nothing -> do
          liftIO $ printf "Types did not match while populating register: %s vs %s\n" (show (C.regType oldEntry)) (show (LLVM.LLVMPointerRepr nr))
          return regsStruct

-- | Generate fresh symbolic variables of supported types
freshSymVar
  :: (CB.IsSymInterface sym, MonadIO m)
  => sym
  -> String
  -> Ctx.Index ctx tp
  -> C.TypeRepr tp
  -> m (C.RegValue' sym tp)
freshSymVar sym prefix idx tp =
  liftIO $ C.RV <$> case W.userSymbol $ prefix ++ show (Ctx.indexVal idx) of
    Right symbol -> case tp of
      LLVM.LLVMPointerRepr w ->
        LLVM.llvmPointer_bv sym
          =<< W.freshConstant sym symbol (W.BaseBVRepr w)
      C.BoolRepr ->
        W.freshConstant sym symbol W.BaseBoolRepr
      _ -> fail $ "unsupported variable type: " ++ show tp
    Left err -> fail $ show err

-- | Create a predicate constraining the IP to be in some executable code segment
genIPConstraint :: ( MonadIO m
                   , 1 <= M.ArchAddrWidth arch
                   , MM.MemWidth (M.ArchAddrWidth arch)
                   , CB.IsSymInterface sym
                   )
                => RefinementContext sym arch
                -> W.SymBV sym (M.ArchAddrWidth arch)
                -- ^ The IP value to constrain
                -> m (W.Pred sym)
genIPConstraint ctx ipVal = liftIO $ do
  let sym = symbolicBackend ctx
  ps <- mapM (genSegConstraint sym (memWidthRepr ctx)) (executableSegments ctx)
  W.andAllOf sym (L.folded . id) ps
  where
    genSegConstraint sym repr seg = do
      let low = MM.segmentOffset seg
      let high = low + MM.segmentSize seg
      lo <- W.bvLit sym repr (fromIntegral low)
      hi <- W.bvLit sym repr (fromIntegral high)
      lb <- W.bvUle sym lo ipVal
      ub <- W.bvUle sym ipVal hi
      W.andPred sym lb ub

-- | Probe the SMT solver for additional models of the given expression up to a maximum @count@
genModels
  :: ( W.OnlineSolver t solver
     , KnownNat w
     , 1 <= w
     , MonadIO m
     , sym ~ CBS.SimpleBackend t fs
     )
  => sym
  -> W.SolverProcess t solver
  -> [W.Pred sym]
  -> W.SymBV sym w
  -> Int
  -> m [W.GroundValue (W.BaseBVType w)]
genModels sym solver_proc assumptions expr count
  | count > 0 = liftIO $ do
    -- solver_proc <- C.getSolverProcess sym
    -- W.checkAndGetModel solver_proc "gen next model" >>= \case
    W.checkWithAssumptionsAndModel solver_proc "Next IP model" assumptions >>= \case
      W.Sat evalFn -> do
        next_ground_val <- W.groundEval evalFn expr
        next_bv_val <- W.bvLit sym W.knownNat next_ground_val
        not_current_ground_val <- W.bvNe sym expr next_bv_val
        -- CB.addAssumption sym $ CB.LabeledPred not_current_ground_val $
        --   CB.AssumptionReason W.initializationLoc "assume different model"
        liftIO $ printf "Generated model: 0x%x\n" next_ground_val
        more_ground_vals <- genModels sym solver_proc (not_current_ground_val : assumptions) expr (count - 1)
        return $ next_ground_val : more_ground_vals
      _ -> return []
  | otherwise = return []

extractIPModels :: ( MS.SymArchConstraints arch
                   , W.OnlineSolver t solver
                   , MonadIO m
                   , CB.IsSymInterface sym
                   , sym ~ CBS.SimpleBackend t fp
                   )
                => RefinementContext sym arch
                -> W.SolverProcess t solver
                -> [W.Pred sym]
                -> M.DiscoveryState arch
                -> WE.Expr t WT.BaseNatType
                -> WE.Expr t (WT.BaseBVType (M.ArchAddrWidth arch))
                -> m (IPModels (MM.MemSegmentOff (M.ArchAddrWidth arch)))
extractIPModels ctx solverProc initialAssumptions discovery_state res_ip_base res_ip_off = do
  liftIO $ putStrLn ("Number of initial assumptions: " ++ show (length initialAssumptions))
  -- FIXME: Make this a parameter
  let modelMax = 10
  let sym = symbolicBackend ctx
  -- liftIO $ C.resetSolverProcess sym
  ip_off_ground_vals <- liftIO $ inFreshAssumptionFrame sym $ do
    -- FIXME: Try to assert that the base of the IP is 0
    ipConstraint <- genIPConstraint ctx res_ip_off
    natZero <- liftIO $ W.natLit sym 0
    basePred <- liftIO $ W.natEq sym natZero res_ip_base
    let assumptions = ipConstraint : basePred : initialAssumptions
    -- let loc = W.mkProgramLoc "" W.InternalPos
    -- let msg = CB.AssumptionReason loc "IP is in executable memory"
    -- CB.addAssumption sym (CB.LabeledPred ipConstraint msg)

    -- let msg2 = CB.AssumptionReason loc "IP is in region 0"
    -- CB.addAssumption sym (CB.LabeledPred basePred msg2)

    liftIO $ putStrLn "IP Formula"
    liftIO $ print (W.printSymExpr res_ip_off)
    genModels sym solverProc assumptions res_ip_off modelMax

  ip_base_mem_word <- resolveIPModelBase ctx res_ip_base

  -- Turn our SMT-generated models into macaw addresses
  let resolveAddr off = M.resolveAbsoluteAddr (M.memory discovery_state) $
                         M.memWord $ fromIntegral $
                         M.memWordToUnsigned ip_base_mem_word + off
  let resolved = mapMaybe resolveAddr ip_off_ground_vals
  liftIO $ putStrLn "Resolved memory addresses of models"
  liftIO $ print resolved
  case length resolved of
    0 -> return NoModels
    nModels | nModels == modelMax -> return SpuriousModels
            | otherwise -> return (Models resolved)

-- |
--
-- NOTE: I expect all of the bases to be zero, as we are generating models based
-- on bitvector IP values (and not structured LLVM Pointer values).  This should
-- be tested.
resolveIPModelBase :: ( MonadIO m
                      , MM.MemWidth (M.ArchAddrWidth arch)
                      , Ord (W.SymExpr sym WT.BaseNatType)
                      , CB.IsSymInterface sym
                      )
                   => RefinementContext sym arch
                   -> W.SymExpr sym WT.BaseNatType -- WE.Expr t WT.BaseNatType
                   -> m (MM.MemWord (M.ArchAddrWidth arch))
resolveIPModelBase ctx res_ip_base =
  case MS.lookupAllocationBase (memPtrTable ctx) res_ip_base of
    Just alloc -> return (MS.allocationBase alloc)
    Nothing
      | Just (W.ConcreteNat 0) <- W.asConcrete res_ip_base ->
        return (M.memWord 0)
      | otherwise ->
        fail (printf "Unexpected IP base: %s" (show (W.printSymExpr res_ip_base)))

initializeSimulator :: ( MonadIO m
                       , 16 <= M.ArchAddrWidth arch
                       , MS.SymArchConstraints arch
                       , CB.IsSymInterface sym
                       , Show (W.SymExpr sym W.BaseNatType)
                       , Show (W.SymExpr sym (W.BaseBVType (M.ArchAddrWidth arch)))
                       )
                    => RefinementContext sym arch
                    -> C.CFG (MS.MacawExt arch) blocks (C.EmptyCtx C.::> C.StructType (MS.CtxToCrucibleType (MS.ArchRegContext arch))) tp
                    -> M.ParsedBlock arch ids
                    -> m (C.ExecState
                            (MS.MacawSimulatorState sym)
                            sym
                            (MS.MacawExt arch)
                            (C.RegEntry sym tp))
initializeSimulator ctx cfg entryBlock = do
  let sym = symbolicBackend ctx
  (memory, initSPVal) <- initializeMemory ctx
  -- FIXME: Capture output somewhere besides stderr
  let halloc = handleAllocator ctx
  let ext = extensionImpl ctx
  let simCtx = C.initSimContext sym LLVM.llvmIntrinsicTypes halloc IO.stderr C.emptyHandleMap ext MS.MacawSimulatorState
  let globalState = C.insertGlobal (memVar ctx) memory C.emptyGlobals
  initRegs <- initialRegisterState ctx memory entryBlock initSPVal
  let simulation = C.regValue <$> C.callCFG cfg initRegs
  let retTy = C.handleReturnType (C.cfgHandle cfg)
  let initState = C.InitialState simCtx globalState C.defaultAbortHandler retTy (C.runOverrideSim retTy simulation)
  return initState

-- | Extend the base memory image (taken from the 'RefinementContext') with a
-- stack (also returning the initial stack pointer value)
initializeMemory :: ( MS.SymArchConstraints arch
                    , 16 <= M.ArchAddrWidth arch
                    , CB.IsSymInterface sym
                    , MonadIO m
                    )
                 => RefinementContext sym arch
                 -> m (LLVM.MemImpl sym, LLVM.LLVMPtr sym (M.ArchAddrWidth arch))
initializeMemory ctx = do
  let ?ptrWidth = W.knownNat
  let sym = symbolicBackend ctx
  let stackBytes = 2 * 1024 * 1024
  stackArray <- liftIO $ W.freshConstant sym (W.safeSymbol "stack") C.knownRepr
  stackSize <- liftIO $ W.bvLit sym ?ptrWidth stackBytes
  (stackBasePtr, mem1) <- liftIO $ LLVM.doMalloc sym LLVM.StackAlloc LLVM.Mutable "stack_alloc" (mem ctx) stackSize LLVM.noAlignment
  mem2 <- liftIO $ LLVM.doArrayStore sym mem1 stackBasePtr LLVM.noAlignment stackArray stackSize
  initSPVal <- liftIO $ LLVM.ptrAdd sym C.knownRepr stackBasePtr stackSize
  return (mem2, initSPVal)


inFreshAssumptionFrame :: (CB.IsBoolSolver sym) => sym -> IO a -> IO a
inFreshAssumptionFrame sym e = do
  fr <- CB.pushAssumptionFrame sym
  res <- e
  _ <- CB.popAssumptionFrame sym fr
  return res
