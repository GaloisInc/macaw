{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Refinement.SymbolicExecution
  ( RefinementContext(..)
  , defaultRefinementContext
  , smtSolveTransfer
  )
where

import           Control.Lens ( (^.) )
import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Discovery as M
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Memory as MS
import           Data.Maybe ( mapMaybe, fromJust )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce
import           Data.Proxy ( Proxy(..) )
import           GHC.TypeNats
import qualified Lang.Crucible.Backend as C
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
import qualified What4.Expr as WE
import qualified What4.Expr.GroundEval as W
import qualified What4.Interface as W
import qualified What4.InterpretedFloatingPoint as WIF
import qualified What4.ProgramLoc as W
import qualified What4.Protocol.Online as W
import qualified What4.SatResult as W

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
  }

defaultRefinementContext
  :: forall arch bin t solver fp
   . ( MS.SymArchConstraints arch
     , 16 <= M.ArchAddrWidth arch
     , W.OnlineSolver t solver
     , WIF.IsInterpretedFloatExprBuilder (C.OnlineBackend t solver fp)
     , t ~ GlobalNonceGenerator
     )
  => C.OnlineBackend t solver fp -- WE.FloatModeRepr fm
  -> MBL.LoadedBinary arch bin
  -- -> (forall solver t . RefinementContext arch t (W.Writer W.Z3) (WE.Flags fm) -> IO a)
  -- -> (forall sym solver t . (sym ~ WE.ExprBuilder t (C.OnlineBackendState (W.Writer W.Z3)) (WE.Flags fm), WIF.IsInterpretedFloatExprBuilder sym) => RefinementContext arch t (W.Writer W.Z3) (WE.Flags fm) -> IO a)
--  -> (forall sym solver t . (sym ~ WE.ExprBuilder t (C.OnlineBackendState solver) (WE.Flags fm), WIF.IsInterpretedFloatExprBuilder sym) => RefinementContext arch t solver (WE.Flags fm) -> IO a)
  -> IO (RefinementContext arch t solver fp)
defaultRefinementContext sym loaded_binary = do
  handle_alloc <- C.newHandleAllocator
  let nonce_gen = globalNonceGenerator
  -- withIONonceGenerator $ \nonce_gen ->
    -- C.withZ3OnlineBackend floatRepr nonce_gen C.NoUnsatFeatures $ \sym ->
  case MS.archVals (Proxy @arch) of
    Just arch_vals -> do

      mem_var <- LLVM.mkMemVar handle_alloc

      (mem, mem_ptr_table) <- MS.newGlobalMemory
        (Proxy @arch)
        sym
        (MS.toCrucibleEndian $ MBL.memoryEndianness loaded_binary)
        MS.ConcreteMutable
        (MBL.memoryImage loaded_binary)

      let ?ptrWidth = W.knownNat
      (base_ptr, allocated_mem) <- LLVM.doMallocUnbounded
        sym
        LLVM.GlobalAlloc
        LLVM.Mutable
        "flat memory"
        mem
        LLVM.noAlignment
      let Right mem_name = W.userSymbol "mem"
      mem_array <- W.freshConstant sym mem_name W.knownRepr
      initialized_mem <- LLVM.doArrayStoreUnbounded
        sym
        allocated_mem
        base_ptr
        LLVM.noAlignment
        mem_array

      let global_mapping_fn = \sym' mem' base off -> do
            flat_mem_ptr <- LLVM.ptrAdd sym' W.knownNat base_ptr off
            MS.mapRegionPointers
              mem_ptr_table
              flat_mem_ptr
              sym'
              mem'
              base
              off

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
          , mem = initialized_mem
          , memPtrTable = mem_ptr_table
          , globalMappingFn = global_mapping_fn
          }
    Nothing -> fail $ "unsupported architecture"

smtSolveTransfer
  :: ( MS.SymArchConstraints arch
     , 16 <= M.ArchAddrWidth arch
     , C.IsSymInterface (C.OnlineBackend t solver fp)
     , W.OnlineSolver t solver
     , MonadIO m
     )
  => RefinementContext arch t solver fp
  -> M.DiscoveryState arch
  -> [M.ParsedBlock arch ids]
  -> m [M.ArchSegmentOff arch]
smtSolveTransfer RefinementContext{..} discovery_state blocks = do
  let ?ptrWidth = W.knownNat

  let Right stack_name = W.userSymbol "stack"
  stack_array <- liftIO $ W.freshConstant symbolicBackend stack_name C.knownRepr
  stack_size <- liftIO $ W.bvLit symbolicBackend ?ptrWidth $ 2 * 1024 * 1024
  (stack_base_ptr, mem1) <- liftIO $ LLVM.doMalloc
    symbolicBackend
    LLVM.StackAlloc
    LLVM.Mutable
    "stack_alloc"
    mem
    stack_size
    LLVM.noAlignment

  mem2 <- liftIO $ LLVM.doArrayStore
    symbolicBackend
    mem1
    stack_base_ptr
    LLVM.noAlignment
    stack_array
    stack_size
  init_sp_val <- liftIO $
    LLVM.ptrAdd symbolicBackend C.knownRepr stack_base_ptr stack_size

  let entry_addr = M.segoffAddr $ M.pblockAddr $ head blocks
  ip_base <- liftIO $ W.natLit symbolicBackend $
    fromIntegral $ M.addrBase entry_addr
  ip_off <- liftIO $ W.bvLit symbolicBackend W.knownNat $
    M.memWordToUnsigned $ M.addrOffset entry_addr
  entry_ip_val <- liftIO $ fromJust <$>
    globalMappingFn symbolicBackend mem2 ip_base ip_off

  init_regs <- initRegs archVals symbolicBackend entry_ip_val init_sp_val
  let posFn = W.BinaryPos "" . maybe 0 fromIntegral . M.segoffAsAbsoluteAddr
  some_cfg <- liftIO $ MS.mkBlockPathCFG
    (MS.archFunctions archVals)
    handleAllocator
    posFn
    blocks
  case some_cfg of
    C.SomeCFG cfg -> do
      let sim_context = C.initSimContext
            symbolicBackend
            LLVM.llvmIntrinsicTypes
            handleAllocator
            IO.stderr
            C.emptyHandleMap
            extensionImpl
            MS.MacawSimulatorState
      let global_state = C.insertGlobal memVar mem2 C.emptyGlobals
      let simulation = C.regValue <$> C.callCFG cfg init_regs
      let handle_return_type = C.handleReturnType $ C.cfgHandle cfg
      let initial_state = C.InitialState
            sim_context
            global_state
            C.defaultAbortHandler
            handle_return_type
            (C.runOverrideSim handle_return_type simulation)
      let execution_features = []
      exec_res <- liftIO $ C.executeCrucible execution_features initial_state
      case exec_res of
        C.FinishedResult _ res -> do
          let res_regs = res ^. C.partialValue . C.gpValue
          case C.regValue $ (MS.lookupReg archVals) res_regs M.ip_reg of
            LLVM.LLVMPointer res_ip_base res_ip_off -> do
              ip_off_ground_vals <- genModels symbolicBackend res_ip_off 10

              ip_base_mem_word <-
                case MS.lookupAllocationBase memPtrTable res_ip_base of
                  Just alloc -> return $ MS.allocationBase alloc
                  Nothing
                    | Just (W.ConcreteNat 0) <- W.asConcrete res_ip_base ->
                      return $ M.memWord 0
                    | otherwise ->
                      fail $ "unexpected ip base: "
                        ++ show (W.printSymExpr res_ip_base)

              return $ mapMaybe
                (\off -> M.resolveAbsoluteAddr (M.memory discovery_state) $
                  M.memWord $ fromIntegral $
                    M.memWordToUnsigned ip_base_mem_word + off)
                ip_off_ground_vals
        C.AbortedResult _ aborted_res -> case aborted_res of
          C.AbortedExec reason _ ->
            fail $ "simulation abort: " ++ show (C.ppAbortExecReason reason)
          C.AbortedExit code ->
            fail $ "simulation halt: " ++ show code
          C.AbortedBranch{} ->
            fail $ "simulation abort branch"
        C.TimeoutResult{} -> fail $ "simulation timeout"

initRegs
  :: forall arch sym m
    . (MS.SymArchConstraints arch, C.IsSymInterface sym, MonadIO m)
  => MS.ArchVals arch
  -> sym
  -> C.RegValue sym (LLVM.LLVMPointerType (M.ArchAddrWidth arch))
  -> C.RegValue sym (LLVM.LLVMPointerType (M.ArchAddrWidth arch))
  -> m (C.RegMap sym (MS.MacawFunctionArgs arch))
initRegs arch_vals sym ip_val sp_val = do
  let reg_types = MS.crucArchRegTypes $ MS.archFunctions $ arch_vals
  reg_vals <- Ctx.traverseWithIndex (freshSymVar sym "reg") reg_types
  let reg_struct = C.RegEntry (C.StructRepr reg_types) reg_vals
  return $ C.RegMap $ Ctx.singleton $
    (MS.updateReg arch_vals)
      ((MS.updateReg arch_vals) reg_struct M.ip_reg ip_val)
      M.sp_reg
      sp_val

freshSymVar
  :: (C.IsSymInterface sym, MonadIO m)
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

genModels
  :: ( C.IsSymInterface (C.OnlineBackend t solver fp)
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
      W.Sat (W.GroundEvalFn{..}) -> do
        next_ground_val <- groundEval expr
        next_bv_val <- W.bvLit sym W.knownNat next_ground_val
        not_current_ground_val <- W.bvNe sym expr next_bv_val
        C.addAssumption sym $ C.LabeledPred not_current_ground_val $
          C.AssumptionReason W.initializationLoc "assume different model"
        more_ground_vals <- genModels sym expr (count - 1)
        return $ next_ground_val : more_ground_vals
      _ -> return []
  | otherwise = return []
