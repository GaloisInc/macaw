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
  , Refinement
  , defaultRefinementContext
  , smtSolveTransfer
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
import           Data.Parameterized.Nonce
import           Data.Proxy ( Proxy(..) )
import           GHC.TypeNats
import qualified Lang.Crucible.Backend as CB
import qualified Lang.Crucible.Backend.Online as C
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
import qualified What4.InterpretedFloatingPoint as WIF
import qualified What4.ProgramLoc as W
import qualified What4.Protocol.Online as W
import qualified What4.SatResult as W

import qualified What4.Expr as WE
import Text.Printf ( printf )
import qualified Text.PrettyPrint.ANSI.Leijen as PP

data RefinementContext arch t solver fp = RefinementContext
  { symbolicBackend :: C.OnlineBackend t solver fp
  , archVals :: MS.ArchVals arch
  , handleAllocator :: C.HandleAllocator
  , nonceGenerator :: NonceGenerator IO t
  , extensionImpl :: C.ExtensionImpl (MS.MacawSimulatorState (C.OnlineBackend t solver fp)) (C.OnlineBackend t solver fp) (MS.MacawExt arch)
  , memVar :: C.GlobalVar LLVM.Mem
  , mem :: LLVM.MemImpl (C.OnlineBackend t solver fp)
  , memPtrTable :: MS.MemPtrTable (C.OnlineBackend t solver fp) (M.ArchAddrWidth arch)
  , globalMappingFn :: MS.GlobalMap (C.OnlineBackend t solver fp) (M.ArchAddrWidth arch)
  , executableSegments :: [MM.MemSegment (M.ArchAddrWidth arch)]
  , memWidthRepr :: PN.NatRepr (M.ArchAddrWidth arch)
  }

type Refinement t solver fp = ( W.OnlineSolver t solver
                              , WIF.IsInterpretedFloatExprBuilder (C.OnlineBackend t solver fp)
                              )

-- | Given a solver backend and binary, create a 'RefinementContext' that has
-- all of the necessary bits to symbolically simulate machine code and query the
-- SMT solver for models of the IP
defaultRefinementContext
  :: forall arch bin t solver fp
   . ( MS.SymArchConstraints arch
     , 16 <= M.ArchAddrWidth arch
     , W.OnlineSolver t solver
     , WIF.IsInterpretedFloatExprBuilder (C.OnlineBackend t solver fp)
     , t ~ GlobalNonceGenerator
     )
  => C.OnlineBackend t solver fp
  -> MBL.LoadedBinary arch bin
  -> IO (RefinementContext arch t solver fp)
defaultRefinementContext sym loaded_binary = do
  handle_alloc <- C.newHandleAllocator
  let nonce_gen = globalNonceGenerator
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
          , nonceGenerator = nonce_gen
          , extensionImpl = ext_impl
          , memVar = mem_var
          , mem = mem0
          , memPtrTable = mem_ptr_table
          , globalMappingFn = global_mapping_fn
          , executableSegments = execSegs
          , memWidthRepr = MM.memWidth (MBL.memoryImage loaded_binary)
          }
    Nothing -> fail $ "unsupported architecture"



smtSolveTransfer
  :: forall arch t solver fp m sym ids
   . ( MS.SymArchConstraints arch
     , 16 <= M.ArchAddrWidth arch
     , CB.IsSymInterface (C.OnlineBackend t solver fp)
     , W.OnlineSolver t solver
     , MonadIO m
     , sym ~ WE.ExprBuilder t (C.OnlineBackendState solver) fp
     )
  => RefinementContext arch t solver fp
  -> M.DiscoveryState arch
  -> [M.ParsedBlock arch ids]
  -> m [M.ArchSegmentOff arch]
smtSolveTransfer ctx discovery_state blocks = do
  let ?ptrWidth = W.knownNat
  let sym = symbolicBackend ctx
  let Right stack_name = W.userSymbol "stack"

  stack_array <- liftIO $ W.freshConstant sym stack_name C.knownRepr
  stack_size <- liftIO $ W.bvLit sym ?ptrWidth $ 2 * 1024 * 1024
  (stack_base_ptr, mem1) <- liftIO $ LLVM.doMalloc
    sym
    LLVM.StackAlloc
    LLVM.Mutable
    "stack_alloc"
    (mem ctx)
    stack_size
    LLVM.noAlignment

  mem2 <- liftIO $ LLVM.doArrayStore
    sym
    mem1
    stack_base_ptr
    LLVM.noAlignment
    stack_array
    stack_size
  init_sp_val <- liftIO $ LLVM.ptrAdd sym C.knownRepr stack_base_ptr stack_size

  -- FIXME: Maintain a Path data type that ensures that the list is non-empty (i.e., get rid of head)
  let entryBlock = head blocks
  init_regs <- initRegs ctx mem2 entryBlock init_sp_val
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
      let sim_context = C.initSimContext
            sym
            LLVM.llvmIntrinsicTypes
            (handleAllocator ctx)
            IO.stderr
            C.emptyHandleMap
            (extensionImpl ctx)
            MS.MacawSimulatorState
      let global_state = C.insertGlobal (memVar ctx) mem2 C.emptyGlobals
      let simulation = C.regValue <$> C.callCFG cfg init_regs
      let handle_return_type = C.handleReturnType $ C.cfgHandle cfg
      let initial_state = C.InitialState
            sim_context
            global_state
            C.defaultAbortHandler
            handle_return_type
            (C.runOverrideSim handle_return_type simulation)
      let execution_features = []
      fr0 <- liftIO $ CB.pushAssumptionFrame sym
      exec_res <- liftIO $ C.executeCrucible execution_features initial_state
      _ <- liftIO $ CB.popAssumptionFrame sym fr0
      case exec_res of
        C.FinishedResult _ res -> do
          let res_regs = res ^. C.partialValue . C.gpValue
          case C.regValue $ (MS.lookupReg (archVals ctx)) res_regs M.ip_reg of
            LLVM.LLVMPointer res_ip_base res_ip_off -> do
              fr1 <- liftIO $ CB.pushAssumptionFrame sym
              ipConstraint <- genIPConstraint ctx res_ip_off
              let loc = W.mkProgramLoc "" W.InternalPos
              let msg = CB.AssumptionReason loc "IP is in executable memory"
              liftIO $ CB.addAssumption sym (CB.LabeledPred ipConstraint msg)
              ip_off_ground_vals <- genModels sym res_ip_off 10
              _ <- liftIO $ CB.popAssumptionFrame sym fr1

              let showAsHex :: Integer -> String
                  showAsHex x = printf "0x%x" x
              liftIO $ putStrLn "\nSMT models:"
              liftIO $ print (fmap showAsHex ip_off_ground_vals)
              ip_base_mem_word <-
                case MS.lookupAllocationBase (memPtrTable ctx) res_ip_base of
                  Just alloc -> return $ MS.allocationBase alloc
                  Nothing
                    | Just (W.ConcreteNat 0) <- W.asConcrete res_ip_base ->
                      return $ M.memWord 0
                    | otherwise ->
                      fail $ "unexpected ip base: "
                        ++ show (W.printSymExpr res_ip_base)

              let resolveAddr off = M.resolveAbsoluteAddr (M.memory discovery_state) $
                                     M.memWord $ fromIntegral $
                                     M.memWordToUnsigned ip_base_mem_word + off
              let resolved = mapMaybe resolveAddr ip_off_ground_vals
              liftIO $ putStrLn "Resolved memory addresses of models"
              liftIO $ print resolved
              return resolved
        C.AbortedResult _ aborted_res -> case aborted_res of
          C.AbortedExec reason _ ->
            fail $ "simulation abort: " ++ show (CB.ppAbortExecReason reason)
          C.AbortedExit code ->
            fail $ "simulation halt: " ++ show code
          C.AbortedBranch{} ->
            fail $ "simulation abort branch"
        C.TimeoutResult{} -> fail $ "simulation timeout"

initRegs :: forall arch sym m solver fp ids t
          . ( MS.SymArchConstraints arch
            , CB.IsSymInterface sym
            , MonadIO m
            , sym ~ C.OnlineBackend t solver fp
            )
  => RefinementContext arch t solver fp
  -> LLVM.MemImpl sym
  -> M.ParsedBlock arch ids
  -> C.RegValue sym (LLVM.LLVMPointerType (M.ArchAddrWidth arch))
  -> m (C.RegMap sym (MS.MacawFunctionArgs arch))
initRegs ctx memory entryBlock spVal = do
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
addKnownRegValue :: forall arch sym m t solver fp tp w
                  . ( MS.SymArchConstraints arch
                    , CB.IsSymInterface sym
                    , MonadIO m
                    , sym ~ C.OnlineBackend t solver fp
                    )
                 => RefinementContext arch t solver fp
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
                   , sym ~ WE.ExprBuilder t (C.OnlineBackendState solver) fp
                   , 1 <= M.ArchAddrWidth arch
                   , MM.MemWidth (M.ArchAddrWidth arch)
                   )
                => RefinementContext arch t solver fp
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
  :: ( CB.IsSymInterface (C.OnlineBackend t solver fp)
     , W.OnlineSolver t solver
     , KnownNat w
     , 1 <= w
     , MonadIO m
     )
  => C.OnlineBackend t solver fp
  -> W.SymBV (C.OnlineBackend t solver fp) w
  -> Int
  -> m [W.GroundValue (W.BaseBVType w)]
genModels sym expr count
  | count > 0 = liftIO $ do
    solver_proc <- C.getSolverProcess sym
    W.checkAndGetModel solver_proc "gen next model" >>= \case
      W.Sat evalFn -> do
        next_ground_val <- W.groundEval evalFn expr
        next_bv_val <- W.bvLit sym W.knownNat next_ground_val
        not_current_ground_val <- W.bvNe sym expr next_bv_val
        CB.addAssumption sym $ CB.LabeledPred not_current_ground_val $
          CB.AssumptionReason W.initializationLoc "assume different model"
        liftIO $ printf "Generated model: 0x%x\n" next_ground_val
        more_ground_vals <- genModels sym expr (count - 1)
        return $ next_ground_val : more_ground_vals
      _ -> return []
  | otherwise = return []
