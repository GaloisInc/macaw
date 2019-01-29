{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
-- | This module uses symbolic evaluation to refine the discovered CFG
-- and resolve unknown transfer classify failures.
--
-- One of the primary refinements possible via this module is the
-- ability to determine transfer targets that were previously
-- undiscoverable.
--
-- For example (roughly tests/samples/switching.c):
--
-- > int retval(int n) {
-- >   switch (n) {
-- >     case 0: ...;
-- >     case 1: ...;
-- >     case 3: ...;
-- >     default: 0;
-- >   }
-- > }
--
-- In the above, the body of each case is relatively small and similar
-- to the others, so the compiler decides not to generate a series of
-- 'cmp n, VAL; jeq CASETGT' instructions, but instead computes an
-- offset based on the maximum size of each case body * n and adds
-- that to the current address.
--
-- discovery:
--   block 1 "setup": terminate with: ite r28 @default-handler @cases-handler
--   block 2 "cases-handler": calculates jump offset for case values, CLASSIFY FAILURE: unknown transfer
--   block 3 "default-handler": terminate with return
--
-- In this example, the jump offset for case values is range-limited
-- by block 1, but block 2 doesn't see that, and also because of that
-- the block(s) corresponding to the case conditions are not
-- discovered.  The goal of the code in this module is to improve
-- this, using SMT analysis.
--
-- First, a What4 formula is generated for block 2 and this is
-- provided to Crucible to identify possible jump targets.  The result
-- should be a nearly infinite number of targets (every "case body
-- size" offset), which Macaw could constrain to the valid text region
-- (although the jumps beyond the text region could arguably be
-- flagged as errors).
--
-- However, by adding the precursor block (block 1) and computing the
-- SMT formula for block 1 + block2, the result of the jump is only
-- the actual case targets, and thus this is a smaller solution (and
-- therefore better) than the previous step.
--
-- The algorithm should continue to iterate back through the blocks to
-- achieve better and better (i.e. smaller) solutions until reaching
-- the entry point of the function itself, or until reaching a point
-- where the solution symbolically diverges (e.g. a loop with a
-- variable exit condition).
--
-- It might be considered an optimization to simply skip the
-- iterations and try to solve from the start of the function to the
-- unknown transfer point, but if there are symbolically-divergent
-- loops in that path the result will be unconstrained (see Note 1).
--
-- In the worst case, the SMT analysis is unable to further refine the
-- information and this block is still noted as an unkown transfer, so
-- it has not worsened the analysis, even though it has not improved
-- it.
--
-- If the refinement does yield a smaller set of functions, that can
-- be identified as the valid targets from this block (e.g. a nested
-- ite), and additionally those targets should be subject to further
-- discovery by Macaw.
--
-- --------------------
-- Note 1: It's theoretically possible that the loop would affect the
-- constraints, but in practice this is fairly unrealistic.  A
-- completely unbounded jump is unlikely to ever be generated for
-- valid compiled C code:
--
-- > int jumpto(int n) {
-- >    (void)(*funcaddr)() = n * 32 + &jumpto;   // unrealistic
-- >    (*funcaddr)();
-- > }
--
-- A jump computation is generally only to target symbols known to the
-- C compiler, and while a section of code that cannot be symbolically
-- resolved (e.g. a symbolically-divergent loop) might *constrain* the
-- target set, the analysis of the portion following the loop should
-- reveal the total set of valid targets:
--
-- > int jumpfor(int n, int l) {
-- >    (int)(*funcs)()[6] = { &jumptgt1, &jumptgt2, ... };
-- >    int tgtnum = n % 3;
-- >    for (int j = 0; j < l; j++) {
-- >      if (j ^ n == 5)
-- >        tgtnum *= 2;
-- >    }
-- >    return (*(funcs[tgtnum]))();
-- > }
--
-- In this case, we hope to discover that the target of the jumps is
-- constrained to the entries in the funcs array, even though the loop
-- cannot be evaluated.


module Data.Macaw.Refinement.UnknownTransfer
  ( symbolicUnkTransferRefinement
  )
where

import           GHC.TypeLits

import Control.Lens
import Control.Monad.ST ( RealWorld, stToIO )
import Data.Macaw.CFG.AssignRhs ( ArchSegmentOff )
import Data.Macaw.Discovery.State ( DiscoveryFunInfo
                                  , DiscoveryState(..)
                                  , ParsedBlock(..)
                                  , ParsedTermStmt(ClassifyFailure)
                                  , blockStatementList
                                  , funInfo
                                  , parsedBlocks
                                  , stmtsTerm
                                  )
import Data.Macaw.Refinement.FuncBlockUtils ( BlockIdentifier, blockID, funForBlock )
import Data.Macaw.Refinement.Path ( FuncBlockPath, buildFuncPath, pathDepth, pathTo, takePath )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Symbolic as MS
import Data.Map (Map)
import Data.Maybe
import qualified Data.Map as Map
import Data.Parameterized.Some
import Data.Parameterized.Nonce
import Data.Semigroup
import Data.Parameterized.Ctx (Ctx)
import qualified Data.Parameterized.Context as Ctx
import Data.Proxy ( Proxy(..) )
import Data.Text (Text)
import qualified Data.Text as Text
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Backend.Online as C
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.LLVM.MemModel as LLVM
import qualified Lang.Crucible.LLVM.Intrinsics as LLVM
import qualified Lang.Crucible.LLVM.DataLayout as LLVM
import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified What4.Expr.GroundEval as W
import qualified What4.Interface as W
import qualified What4.ProgramLoc as W
import qualified What4.Protocol.Online as W
import qualified What4.Protocol.SMTLib2 as W
import qualified What4.SatResult as W
import qualified What4.Solver.Z3 as W
import           System.IO as IO


-- | This is the main entrypoint, which is given the current Discovery
-- information and which attempts to resolve UnknownTransfer
-- classification failures, returning (possibly updated) Discovery
-- information.
symbolicUnkTransferRefinement :: DiscoveryState arch -> DiscoveryState arch
symbolicUnkTransferRefinement = refineTransfers []


-- | The main loop for transfer discovery refinement.  The first
-- argument is the accumulation of UnknownTransfer failures that
-- refinement has failed for and therefore should not be considered
-- for further refinement.  This is because refinement may reveal new
-- Blocks, which themselves may have unrefined terminators, so this
-- function recurses until there are no more UnknownTransfer failure
-- blocks in the input discovery state that are not also in the
-- failure accumulation array.
refineTransfers :: [BlockIdentifier arch]
                   -- ^ attempted blocks
                -> DiscoveryState arch
                   -- ^ input DiscoveryState
                -> DiscoveryState arch
                   -- ^ Possibly updated DiscoveryState
refineTransfers failedRefine inpDS =
  let unrefineable = flip elem failedRefine . blockID
      unkTransfers = inpDS ^. funInfo
                     . to getAllFunctionsTransfers
                     ^..folded
                     . filtered (not . unrefineable)
      thisUnkTransfer = head unkTransfers
      thisId = blockID thisUnkTransfer
  in if null unkTransfers
     then inpDS
     else case refineBlockTransfer inpDS thisUnkTransfer of
            Nothing    -> refineTransfers (thisId : failedRefine) inpDS
            Just updDS -> refineTransfers failedRefine updDS


getAllFunctionsTransfers :: Map (ArchSegmentOff arch)
                                  (Some (DiscoveryFunInfo arch))
                         -> [Some (ParsedBlock arch)]
getAllFunctionsTransfers = concatMap getUnknownTransfers . Map.elems


getUnknownTransfers :: (Some (DiscoveryFunInfo arch))
                    -> [Some (ParsedBlock arch)]
getUnknownTransfers (Some fi) =
  Some <$> (filter isUnknownTransfer $ Map.elems $ fi ^. parsedBlocks)

isUnknownTransfer :: ParsedBlock arch ids -> Bool
isUnknownTransfer pb =
  case stmtsTerm (blockStatementList pb) of
    ClassifyFailure {} -> True
    _ -> False

-- | This function attempts to use an SMT solver to refine the block
-- transfer.  If the transfer can be resolved, it will update the
-- input DiscoveryState with the new block information (plus any
-- blocks newly discovered via the transfer resolution) and return
-- that.  If it was unable to refine the transfer, it will return
-- Nothing and this block will be added to the "unresolvable" list.
refineBlockTransfer :: DiscoveryState arch
                    -> Some (ParsedBlock arch)
                    -> Maybe (DiscoveryState arch)
refineBlockTransfer inpDS blk =
  let path = buildFuncPath <$> funForBlock blk inpDS
  in case path >>= pathTo (blockID blk) of
       Nothing -> error "unable to find function path for block" -- internal error
       Just p -> do soln <- refinePath inpDS p (pathDepth p) 0 Nothing
                    return $ updateDiscovery soln blk inpDS


updateDiscovery :: Solution
                -> Some (ParsedBlock arch)
                -> DiscoveryState arch
                -> DiscoveryState arch
updateDiscovery _soln _pblk _inpDS = undefined  -- add replace pblk with soln, and add new blocks discoverd by soln


refinePath inpDS path maxlevel numlevels prevResult =
  let thispath = takePath numlevels path
      smtEquation = equationFor inpDS thispath
  in case solve smtEquation of
       Nothing -> prevResult -- divergent, stop here
       Just soln -> let nextlevel = numlevels + 1
                        bestResult = case prevResult of
                                       Nothing -> Just soln
                                       Just prevSoln ->
                                         if soln `isBetterSolution` prevSoln
                                         then Just soln
                                         else prevResult
                    in if numlevels > maxlevel
                       then bestResult
                       else refinePath inpDS path maxlevel nextlevel bestResult

data Equation = Equation  -- replace by What4 expression to pass to Crucible
data Solution = Solution  -- replace by Crucible output

equationFor :: DiscoveryState arch -> FuncBlockPath arch -> Equation
equationFor inpDS path = undefined

solve :: Equation -> Maybe Solution
solve _eqn = Just Solution

isBetterSolution :: Solution -> Solution -> Bool
isBetterSolution _solnA _solnB = True  -- TBD

----------------------------------------------------------------------
-- * Symbolic execution


data RefinementContext arch t solver fp = RefinementContext
  { symbolicBackend :: C.OnlineBackend t solver fp
  , archVals :: MS.ArchVals arch
  , handleAllocator :: C.HandleAllocator RealWorld
  , nonceGenerator :: NonceGenerator IO t
  , extensionImpl :: C.ExtensionImpl (MS.MacawSimulatorState (C.OnlineBackend t solver fp)) (C.OnlineBackend t solver fp) (MS.MacawExt arch)
  , memVar :: C.GlobalVar LLVM.Mem
  }

withDefaultRefinementContext
  :: forall arch a
   . MS.ArchInfo arch
  => (forall t . RefinementContext arch t (W.Writer W.Z3) (C.Flags C.FloatIEEE) -> IO a)
  -> IO a
withDefaultRefinementContext k = do
  handle_alloc <- C.newHandleAllocator
  withIONonceGenerator $ \nonce_gen ->
    C.withZ3OnlineBackend nonce_gen C.NoUnsatFeatures $ \sym ->
      case MS.archVals (Proxy @arch) of
        Just arch_vals -> do
          mem_var <- stToIO $ LLVM.mkMemVar handle_alloc
          MS.withArchEval (arch_vals) sym $ \arch_eval_fns -> do
            let ext_impl = MS.macawExtensions
                  arch_eval_fns
                  mem_var
                  (\sym _ _ off -> Just <$> LLVM.llvmPointer_bv sym off)
                  (MS.LookupFunctionHandle $ \_ _ _ -> undefined)
            k $ RefinementContext
              { symbolicBackend = sym
              , archVals = arch_vals
              , handleAllocator = handle_alloc
              , nonceGenerator = nonce_gen
              , extensionImpl = ext_impl
              , memVar = mem_var
              }
        Nothing -> fail $ "unsupported architecture"

freshSymVar
  :: C.IsSymInterface sym
  => sym
  -> String
  -> Ctx.Index ctx tp
  -> C.TypeRepr tp
  -> IO (C.RegValue' sym tp)
freshSymVar sym prefix idx tp =
  C.RV <$> case W.userSymbol $ prefix ++ show (Ctx.indexVal idx) of
    Right symbol -> case tp of
      LLVM.LLVMPointerRepr w ->
        LLVM.llvmPointer_bv sym
          =<< W.freshConstant sym symbol (W.BaseBVRepr w)
      C.BoolRepr ->
        W.freshConstant sym symbol W.BaseBoolRepr
      _ -> fail $ "unsupported variable type: " ++ show tp
    Left err -> fail $ show err

initRegs
  :: forall arch sym
   . (MS.SymArchConstraints arch, C.IsSymInterface sym)
  => MS.ArchVals arch
  -> sym
  -> C.RegValue sym (LLVM.LLVMPointerType (MC.ArchAddrWidth arch))
  -> IO (C.RegMap sym (MS.MacawFunctionArgs arch))
initRegs arch_vals sym ip_val = do
  let reg_types = MS.crucArchRegTypes $ MS.archFunctions $ arch_vals
  reg_vals <- Ctx.traverseWithIndex (freshSymVar sym "reg") reg_types
  let reg_struct = C.RegEntry (C.StructRepr reg_types) reg_vals
  return $ C.RegMap $ Ctx.singleton $
    (MS.updateReg arch_vals) reg_struct (MC.ip_reg @(MC.ArchReg arch)) ip_val

refineBlockTransfer'
  :: forall arch t solver fp
   . ( MS.SymArchConstraints arch
     , C.IsSymInterface (C.OnlineBackend t solver fp)
     , W.OnlineSolver t solver
     )
  => RefinementContext arch t solver fp
  -> DiscoveryState arch
  -> Some (ParsedBlock arch)
  -> IO [ArchSegmentOff arch]
refineBlockTransfer' RefinementContext{..} discovery_state (Some block) = do
  let arch = Proxy @arch
  block_ip_val <- case MC.segoffAsAbsoluteAddr (pblockAddr block) of
    Just addr -> LLVM.llvmPointer_bv symbolicBackend
      =<< W.bvLit symbolicBackend W.knownNat (fromIntegral addr)
    Nothing -> fail $ "unexpected block address: " ++ show (pblockAddr block)
  init_regs <- initRegs archVals symbolicBackend block_ip_val
  init_mem <- LLVM.emptyMem LLVM.LittleEndian
  some_cfg <- stToIO $ MS.mkParsedBlockCFG
    (MS.archFunctions archVals)
    handleAllocator
    Map.empty
    (W.BinaryPos "" . maybe 0 fromIntegral . MC.segoffAsAbsoluteAddr)
    block
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
      let global_state = C.insertGlobal
            memVar
            init_mem
            C.emptyGlobals
      let simulation = C.regValue <$> C.callCFG cfg init_regs
      let handle_return_type = C.handleReturnType $ C.cfgHandle cfg
      let initial_state = C.InitialState
            sim_context
            global_state
            C.defaultAbortHandler
            (C.runOverrideSim handle_return_type simulation)
      let execution_features = []
      exec_res <- C.executeCrucible execution_features initial_state
      case exec_res of
        C.FinishedResult _ res -> do
          let res_regs = res ^. C.partialValue . C.gpValue
          let res_ip = (MS.lookupReg archVals)
                res_regs
                (MC.ip_reg @(MC.ArchReg arch))
          res_ip_bv_val <- LLVM.projectLLVM_bv
            symbolicBackend
            (C.regValue res_ip)
          ip_ground_vals <- genModels symbolicBackend res_ip_bv_val 10
          return $ mapMaybe
            (MC.resolveAbsoluteAddr (memory discovery_state) . MC.memWord . fromIntegral)
            ip_ground_vals
        _ -> fail "simulation failed"

genModels
  :: ( C.IsSymInterface (C.OnlineBackend t solver fp)
     , W.OnlineSolver t solver
     , KnownNat w
     , 1 <= w
     )
  => C.OnlineBackend t solver fp
  -> W.SymBV (C.OnlineBackend t solver fp) w
  -> Int
  -> IO [W.GroundValue (W.BaseBVType w)]
genModels sym expr count
  | count > 0 = do
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