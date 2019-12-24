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
  ( RefinementConfig(..)
  , defaultRefinementConfig
  , RefinementContext(..)
  , defaultRefinementContext
  , smtSolveTransfer
  , IPModels(..)
  , ipModels
  )
where

import qualified Control.Lens as L
import           Control.Lens ( (^.) )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
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
import qualified Data.Traversable as T
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
import qualified What4.Expr.GroundEval as W
import qualified What4.Interface as W
import qualified What4.ProgramLoc as W
import qualified What4.Protocol.Online as W
import qualified What4.SatResult as W
import qualified What4.BaseTypes as WT
import qualified What4.LabeledPred as WLP

import qualified Data.Macaw.Refinement.Path as RP
import qualified Data.Macaw.Refinement.Solver as MRS

import qualified What4.Expr as WE
import Text.Printf ( printf )

data RefinementConfig =
  RefinementConfig { solver :: MRS.Solver
                   -- ^ The solver to use to find models
                   , solverInteractionFile :: Maybe FilePath
                   -- ^ An optional file to record solver interactions (queries sent and responses)
                   , maximumModelCount :: Int
                   -- ^ The maximum number of IP models to produce for any
                   -- indirect call; reaching this number will be taken as an
                   -- indication that the problem is under-constrained and
                   -- macaw-refinement will give up on the branch.
                   , parallelismFactor :: Int
                   -- ^ The number of simultaneous solver instances (the default and minimum is 1)
                   }

defaultRefinementConfig :: RefinementConfig
defaultRefinementConfig =
  RefinementConfig { solver = MRS.Yices
                   , solverInteractionFile = Nothing
                   , maximumModelCount = 20
                   , parallelismFactor = 1
                   }

data RefinementContext arch = RefinementContext
  { executableSegments :: [MM.MemSegment (M.ArchAddrWidth arch)]
  -- ^ The segments in the binary being analyzed that contain code
  , memWidthRepr :: PN.NatRepr (M.ArchAddrWidth arch)
  -- ^ The width of pointers for the platform
  , binaryEndianness :: M.Endianness
  , binaryMemory :: M.Memory (M.ArchAddrWidth arch)
  , config :: RefinementConfig
  }

-- | Given a solver backend and binary, create a 'RefinementContext' that has
-- all of the necessary bits to symbolically simulate machine code and query the
-- SMT solver for models of the IP
defaultRefinementContext
  :: forall arch bin
   . ( MS.SymArchConstraints arch
     , 16 <= M.ArchAddrWidth arch
     )
  => RefinementConfig
  -> MBL.LoadedBinary arch bin
  -> IO (RefinementContext arch)
defaultRefinementContext cfg loaded_binary = do
  let isExecutable = MMP.isExecutable . MM.segmentFlags
  let execSegs = filter isExecutable (MM.memSegments (MBL.memoryImage loaded_binary))
  return $ RefinementContext
    { executableSegments = execSegs
    , memWidthRepr = MM.memWidth (MBL.memoryImage loaded_binary)
    , binaryEndianness = MBL.memoryEndianness loaded_binary
    , binaryMemory = MBL.memoryImage loaded_binary
    , config = cfg
    }

-- | A data type to represent the models we get back from the solver
--
-- This lets us distinguish between no models and too many models (exceeding the
-- number requested, probably indicating that they are spurious)
data IPModels a = NoModels
                | Models [a]
                | SpuriousModels
                | Timeout
                | Error String

-- | Returns all models (unless there is a spurious result)
ipModels :: IPModels a -> Maybe [a]
ipModels m =
  case m of
    NoModels -> Just []
    Models ms -> Just ms
    SpuriousModels -> Nothing
    Error {} -> Nothing
    Timeout -> Nothing

smtSolveTransfer
  :: forall arch m ids
   . ( MS.SymArchConstraints arch
     , 16 <= M.ArchAddrWidth arch
     , MonadIO m
     )
  => RefinementContext arch
  -> RP.CFGSlice arch ids -- [M.ParsedBlock arch ids]
  -> m (IPModels (M.ArchSegmentOff arch))
smtSolveTransfer ctx slice
  | Just archVals <- MS.archVals (Proxy @arch) = MRS.withNewBackend (solver (config ctx)) $ \(_proxy :: proxy solver) problemFeatures (sym :: CBS.SimpleBackend t fs) -> do
      halloc <- liftIO $ C.newHandleAllocator

      -- FIXME: Maintain a Path data type that ensures that the list is non-empty (i.e., get rid of head)
      let (entryBlock, body, targetBlock) = RP.sliceComponents slice
      -- let entryBlock = head blocks
      let posFn = W.BinaryPos "" . maybe 0 fromIntegral . M.segoffAsAbsoluteAddr
      some_cfg <- liftIO $ MS.mkBlockSliceCFG
        (MS.archFunctions archVals)
        halloc
        posFn
        entryBlock
        body
        [targetBlock]

      -- F.forM_ (entryBlock : targetBlock : body) $ \pb -> liftIO $ do
      --   printf "Block %s\n" (show (M.pblockAddr pb))
      --   putStrLn (show (PP.pretty pb))

      case some_cfg of
        C.SomeCFG cfg -> do
          let executionFeatures = []
          initialState <- initializeSimulator ctx sym archVals halloc cfg entryBlock

          -- Symbolically execute the relevant code in a fresh assumption
          -- environment so that we can avoid polluting the global solver state
          -- exec_res <- liftIO $ inFreshAssumptionFrame sym $ do
          --
          -- NOTE: The current code isn't using a fresh frame.  It turns out that we
          -- really do want the path conditions established during symbolic
          -- execution in scope, or we are in trouble (e.g., we won't have bounds on
          -- jump tables)
          exec_res <- liftIO $
            C.executeCrucible executionFeatures initialState

          assumptions <- F.toList . fmap (^. WLP.labeledPred) <$> liftIO (CB.collectAssumptions sym)

          case exec_res of
            C.FinishedResult _ res -> do
              let res_regs = res ^. C.partialValue . C.gpValue
              case C.regValue $ (MS.lookupReg archVals) res_regs M.ip_reg of
                LLVM.LLVMPointer res_ip_base res_ip_off -> do
                  hdl <- T.traverse (\fn -> liftIO (IO.openFile fn IO.WriteMode)) (solverInteractionFile (config ctx))
                  solverProc :: W.SolverProcess t solver
                             <- liftIO $ W.startSolverProcess problemFeatures hdl sym
                  models <- extractIPModels ctx sym solverProc assumptions res_ip_base res_ip_off
                  _ <- liftIO $ W.shutdownSolverProcess solverProc
                  return models
            C.AbortedResult _ aborted_res -> case aborted_res of
              C.AbortedExec reason _ ->
                return (Error ("simulation abort: " ++ show (CB.ppAbortExecReason reason)))
              C.AbortedExit code ->
                return (Error ("simulation halt: " ++ show code))
              C.AbortedBranch{} ->
                return (Error "simulation abort branch")
            C.TimeoutResult{} ->
              return Timeout
  | otherwise = fail "Unsupported architecture"


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
                     => sym
                     -> MS.ArchVals arch
                     -> MS.GlobalMap sym (M.ArchAddrWidth arch)
                     -> LLVM.MemImpl sym
                     -- ^ The memory state to start from
                     -> M.ParsedBlock arch ids
                     -- ^ The entry block of the path
                     -> C.RegValue sym (LLVM.LLVMPointerType (M.ArchAddrWidth arch))
                     -- ^ The stack pointer to use
                     -> m (C.RegMap sym (MS.MacawFunctionArgs arch))
initialRegisterState sym archVals globalMappingFn memory entryBlock spVal = do
  -- Build an IP value to populate the initial register state with
  let entryAddr = M.segoffAddr (M.pblockAddr entryBlock)
  ip_base <- liftIO $ W.natLit sym (fromIntegral (M.addrBase entryAddr))
  ip_off <- liftIO $ W.bvLit sym W.knownNat (M.memWordToUnsigned (M.addrOffset entryAddr))
  entryIPVal <- liftIO $ globalMappingFn sym memory ip_base ip_off

  -- liftIO $ printf "Entry initial state"
  -- liftIO $ print (M.blockAbstractState entryBlock)

  let reg_types = MS.crucArchRegTypes (MS.archFunctions archVals)
  reg_vals <- Ctx.traverseWithIndex (freshSymVar sym "reg") reg_types
  let reg_struct0 = C.RegEntry (C.StructRepr reg_types) reg_vals
  let reg_struct1 = MS.updateReg archVals reg_struct0 M.ip_reg entryIPVal
  let reg_struct2 = MS.updateReg archVals reg_struct1 M.sp_reg spVal

  let absRegs = M.blockAbstractState entryBlock ^. MAA.absRegState
  reg_struct <- MapF.foldlMWithKey (addKnownRegValue sym archVals globalMappingFn memory) reg_struct2 (M.regStateMap absRegs)

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
                 => sym
                 -> MS.ArchVals arch
                 -> MS.GlobalMap sym (M.ArchAddrWidth arch)
                 -> LLVM.MemImpl sym
                 -> C.RegEntry sym (MS.ArchRegStruct arch)
                 -> M.ArchReg arch tp
                 -> MAA.AbsValue w tp
                 -> m (C.RegEntry sym (MS.ArchRegStruct arch))
addKnownRegValue sym archVals globalMappingFn memory regsStruct reg val =
  case val of
    MAA.FinSet bvs
      | [singleBV] <- F.toList bvs -> do
          base <- liftIO $ W.natLit sym 0
          let oldEntry = MS.lookupReg archVals regsStruct reg
          let ptrWidthRepr = W.knownNat @(M.ArchAddrWidth arch)
          case testEquality (C.regType oldEntry) (LLVM.LLVMPointerRepr ptrWidthRepr) of
            Just Refl -> do
              -- This is a value with the same width as a pointer.  We attempt
              -- to translate it into a pointer using the global map if possible
              off <- liftIO $ W.bvLit sym ptrWidthRepr singleBV
              ptr <- liftIO $ globalMappingFn sym memory base off
              return (MS.updateReg archVals regsStruct reg ptr)
            Nothing ->
              case C.regType oldEntry of
                LLVM.LLVMPointerRepr nr -> do
                  -- Otherwise, this is just a bitvector of a non-pointer size,
                  -- so we just make it into a plain bitvector.
                  bvVal <- liftIO $ W.bvLit sym nr singleBV
                  let ptr = LLVM.LLVMPointer base bvVal
                  return (MS.updateReg archVals regsStruct reg ptr)
                _ -> return regsStruct
    _ -> return regsStruct

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
        -- FIXME: This makes a symbolic bitvector - the block ID should also be symbolic
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
                => RefinementContext arch
                -> sym
                -> W.SymBV sym (M.ArchAddrWidth arch)
                -- ^ The IP value to constrain
                -> m (W.Pred sym)
genIPConstraint ctx sym ipVal = liftIO $ do
  ps <- mapM (genSegConstraint (memWidthRepr ctx)) (executableSegments ctx)
  W.andAllOf sym (L.folded . id) ps
  where
    genSegConstraint repr seg = do
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
    W.checkWithAssumptionsAndModel solver_proc "Next IP model" assumptions >>= \case
      W.Sat evalFn -> do
        next_ground_val <- W.groundEval evalFn expr
        next_bv_val <- W.bvLit sym W.knownNat next_ground_val
        not_current_ground_val <- W.bvNe sym expr next_bv_val
        liftIO $ printf "Generated model: 0x%x\n" next_ground_val
        more_ground_vals <- genModels sym solver_proc (not_current_ground_val : assumptions) expr (count - 1)
        return $ next_ground_val : more_ground_vals
      _ -> return []
  | otherwise = return []

extractIPModels :: forall arch solver m sym t fp
                 . ( MS.SymArchConstraints arch
                   , W.OnlineSolver t solver
                   , MonadIO m
                   , CB.IsSymInterface sym
                   , sym ~ CBS.SimpleBackend t fp
                   )
                => RefinementContext arch
                -> sym
                -> W.SolverProcess t solver
                -> [W.Pred sym]
                -> WE.Expr t WT.BaseNatType
                -> WE.Expr t (WT.BaseBVType (M.ArchAddrWidth arch))
                -> m (IPModels (MM.MemSegmentOff (M.ArchAddrWidth arch)))
extractIPModels ctx sym solverProc initialAssumptions res_ip_base res_ip_off = do
  let modelMax = maximumModelCount (config ctx)
  ip_off_ground_vals <- liftIO $ inFreshAssumptionFrame sym $ do
    -- Assert that the IP is in an executable segment
    ipConstraint <- genIPConstraint ctx sym res_ip_off

    -- We also want to assert that the IP is either a plain bitvector (region 0)
    -- or in our global memory region (region 1)
    natZero <- liftIO $ W.natLit sym 0
    natOne <- liftIO $ W.natLit sym 1
    basePred0 <- liftIO $ W.natEq sym natZero res_ip_base
    basePred1 <- liftIO $ W.natEq sym natOne res_ip_base
    basePred <- liftIO $ W.orPred sym basePred0 basePred1

    let assumptions = ipConstraint : basePred : initialAssumptions

    -- liftIO $ putStrLn "IP Formula"
    -- liftIO $ print (W.printSymExpr res_ip_off)
    genModels sym solverProc assumptions res_ip_off modelMax

  let ip_base_mem_word :: MM.MemWord (M.ArchAddrWidth arch)
      ip_base_mem_word = M.memWord 0

  -- Turn our SMT-generated models into macaw addresses
  let resolveAddr off = M.resolveAbsoluteAddr (binaryMemory ctx) $
                         M.memWord $ fromIntegral $
                         M.memWordToUnsigned ip_base_mem_word + off
  let resolved = mapMaybe resolveAddr ip_off_ground_vals
  liftIO $ putStrLn "Resolved memory addresses of models"
  liftIO $ print resolved
  case length resolved of
    0 -> return NoModels
    nModels | nModels == modelMax -> return SpuriousModels
            | otherwise -> return (Models resolved)

initializeSimulator :: forall m sym arch blocks ids tp
                     . ( MonadIO m
                       , 16 <= M.ArchAddrWidth arch
                       , MS.SymArchConstraints arch
                       , CB.IsSymInterface sym
                       , Show (W.SymExpr sym W.BaseNatType)
                       , Show (W.SymExpr sym (W.BaseBVType (M.ArchAddrWidth arch)))
                       , Ord (W.SymExpr sym WT.BaseNatType)
                       )
                    => RefinementContext arch
                    -> sym
                    -> MS.ArchVals arch
                    -> C.HandleAllocator
                    -> C.CFG (MS.MacawExt arch) blocks (C.EmptyCtx C.::> C.StructType (MS.CtxToCrucibleType (MS.ArchRegContext arch))) tp
                    -> M.ParsedBlock arch ids
                    -> m (C.ExecState
                            (MS.MacawSimulatorState sym)
                            sym
                            (MS.MacawExt arch)
                            (C.RegEntry sym tp))
initializeSimulator ctx sym archVals halloc cfg entryBlock = MS.withArchEval archVals sym $ \archEvalFns -> do
  memVar <- liftIO $ LLVM.mkMemVar halloc
  let end = MS.toCrucibleEndian (binaryEndianness ctx)
  (memory0, memPtrTable) <- liftIO $ MS.newGlobalMemory (Proxy @arch) sym end MS.ConcreteMutable (binaryMemory ctx)
  (memory1, initSPVal) <- initializeMemory (Proxy @arch) sym memory0
  -- FIXME: Capture output somewhere besides stderr
  let globalMappingFn = MS.mapRegionPointers memPtrTable
  let lookupHdl = MS.LookupFunctionHandle $ \_ _ _ -> error "Function calls not supported"
  let mkPtrPred = MS.mkGlobalPointerValidityPred memPtrTable
  let ext = MS.macawExtensions archEvalFns memVar globalMappingFn lookupHdl mkPtrPred
  let simCtx = C.initSimContext sym LLVM.llvmIntrinsicTypes halloc IO.stderr C.emptyHandleMap ext MS.MacawSimulatorState
  let globalState = C.insertGlobal memVar memory1 C.emptyGlobals
  initRegs <- initialRegisterState sym archVals globalMappingFn memory1 entryBlock initSPVal
  let simulation = C.regValue <$> C.callCFG cfg initRegs
  let retTy = C.handleReturnType (C.cfgHandle cfg)
  let initState = C.InitialState simCtx globalState C.defaultAbortHandler retTy (C.runOverrideSim retTy simulation)
  return initState

-- | Extend the base memory image (taken from the 'RefinementContext') with a
-- stack (also returning the initial stack pointer value)
initializeMemory :: forall arch sym m proxy
                  . ( MS.SymArchConstraints arch
                    , 16 <= M.ArchAddrWidth arch
                    , CB.IsSymInterface sym
                    , MonadIO m
                    )
                 => proxy arch
                 -> sym
                 -> LLVM.MemImpl sym
                 -> m (LLVM.MemImpl sym, LLVM.LLVMPtr sym (M.ArchAddrWidth arch))
initializeMemory _ sym mem = do
  let ?ptrWidth = W.knownNat
  let stackBytes = 2 * 1024 * 1024
  stackArray <- liftIO $ W.freshConstant sym (W.safeSymbol "stack") C.knownRepr
  stackSize <- liftIO $ W.bvLit sym ?ptrWidth stackBytes
  stackSizex2 <- liftIO $ W.bvLit sym ?ptrWidth (2 * stackBytes)
  (stackBasePtr, mem1) <- liftIO $ LLVM.doMalloc sym LLVM.StackAlloc LLVM.Mutable "stack_alloc" mem stackSizex2 LLVM.noAlignment
  mem2 <- liftIO $ LLVM.doArrayStore sym mem1 stackBasePtr LLVM.noAlignment stackArray stackSize
  initSPVal <- liftIO $ LLVM.ptrAdd sym C.knownRepr stackBasePtr stackSize
  return (mem2, initSPVal)


inFreshAssumptionFrame :: (CB.IsBoolSolver sym) => sym -> IO a -> IO a
inFreshAssumptionFrame sym e = do
  fr <- CB.pushAssumptionFrame sym
  res <- e
  _ <- CB.popAssumptionFrame sym fr
  return res
