{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.Symbolic
  ( ArchStepInfo(..)
  , stepBlocks
  ) where

import           Control.Monad.Except
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Ctx
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableFC
import           Data.String
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.CFG.SSAConversion as C
import qualified Lang.Crucible.Config as C
import qualified Lang.Crucible.FunctionHandle as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C
import qualified Lang.Crucible.Simulator.OverrideSim as C
import qualified Lang.Crucible.Simulator.RegMap as C
import           Lang.Crucible.Solver.Interface
import           Numeric (showHex)
import           System.IO (stdout)

import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.CFG.Core as M
import qualified Data.Macaw.Memory as M
import qualified Data.Macaw.Types as M

import           Data.Macaw.Symbolic.App

data MacawSimulatorState sym = MacawSimulatorState

-- | Create the variables from a collection of registers.
regVars :: (IsSymInterface sym, M.HasRepr reg M.TypeRepr)
        => sym
        -> (forall tp . reg tp -> SolverSymbol)
        -> Ctx.Assignment reg ctx
        -> IO (Ctx.Assignment (C.RegValue' sym) (CtxToCrucibleType ctx))
regVars sym nameFn a =
  case Ctx.view a of
    Ctx.AssignEmpty -> pure Ctx.empty
    Ctx.AssignExtend b reg -> do
      varAssign <- regVars sym nameFn b
      c <- freshConstant sym (nameFn reg) (typeToCrucibleBase (M.typeRepr reg))
      pure (varAssign Ctx.%> C.RV c)

runFreshSymOverride :: M.TypeRepr tp
                    -> C.OverrideSim MacawSimulatorState sym ret
                                     Ctx.EmptyCtx
                                     (ToCrucibleType tp)
                                     (C.RegValue sym (ToCrucibleType tp))
runFreshSymOverride = undefined

runReadMemOverride :: NatRepr w
                   -> M.MemRepr tp
                   -> C.OverrideSim MacawSimulatorState sym ret
                                    (EmptyCtx ::> C.BVType w)
                                    (ToCrucibleType tp)
                                    (C.RegValue sym (ToCrucibleType tp))
runReadMemOverride = undefined

runWriteMemOverride :: NatRepr w
                    -> M.MemRepr tp
                    -> C.OverrideSim MacawSimulatorState sym ret
                                     (EmptyCtx ::> C.BVType w ::> ToCrucibleType tp)
                                     C.UnitType
                                     (C.RegValue sym C.UnitType)
runWriteMemOverride = undefined

{-
runSyscallOverride :: CrucGenContext arch ids s
                   -> C.OverrideSim MacawSimulatorState sym ret
                                    (EmptyCtx ::> ArchRegStruct arch)
                                    (ArchRegStruct arch)
                                    (C.RegValue sym (ArchRegStruct arch))
runSyscallOverride = undefined
-}

createHandleBinding :: CrucGenContext arch ids s
                    -> HandleId arch '(args, rtp)
                    -> C.OverrideSim MacawSimulatorState sym ret args rtp (C.RegValue sym rtp)
createHandleBinding ctx hid =
  case hid of
    MkFreshSymId repr -> runFreshSymOverride repr
    ReadMemId repr    -> runReadMemOverride (archWidthRepr ctx) repr
    WriteMemId repr   -> runWriteMemOverride (archWidthRepr ctx) repr
    SyscallId         -> undefined

-- | This function identifies all the handles needed, and returns
-- function bindings for each one.
createHandleMap :: forall arch ids s sym
                .  CrucGenContext arch ids s
                -> UsedHandleSet arch
                -> C.FunctionBindings MacawSimulatorState sym
createHandleMap ctx = MapF.foldrWithKey go C.emptyHandleMap
  where go :: HandleId arch pair
           -> HandleVal pair
           -> C.FunctionBindings MacawSimulatorState sym
           -> C.FunctionBindings MacawSimulatorState sym
        go hid (HandleVal h) b =
          let o = C.mkOverride' (handleIdName hid) (handleIdRetType ctx hid) (createHandleBinding ctx hid)
           in  C.insertHandleMap h (C.UseOverride o) b

data ArchStepInfo arch
  = ArchStepInfo
  { archRegNameFn :: !(forall tp . M.ArchReg arch tp -> SolverSymbol)
  , archRegAssignment :: !(Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch))
  , archTranslateFn :: !(forall ids s tp
                         . M.ArchFn arch ids tp
                         -> CrucGen arch ids s (CR.Atom s (ToCrucibleType tp)))
     -- ^ Function for translating an architecture specific function
  , archTranslateStmt :: !(forall ids s . M.ArchStmt arch ids -> CrucGen arch ids s ())
  }


mkMemSegmentBinding :: (1 <= w)
                    => C.HandleAllocator s
                    -> NatRepr w
                    -> M.MemSegment w
                    -> ST s (M.SegmentIndex, C.GlobalVar (C.BVType w))
mkMemSegmentBinding halloc awidth seg = do
  let nm = Text.pack ("MemSegmentBase" ++ show (M.segmentIndex seg))
  gv <- CR.freshGlobalVar halloc nm (C.BVRepr awidth)
  pure $ (M.segmentIndex seg, gv)

mkMemSegmentMap :: (1 <= w)
                => C.HandleAllocator s
                -> M.Memory w
                -> ST s (MemSegmentMap w)
mkMemSegmentMap halloc mem = do
  let isVirt seg = isNothing (M.segmentBase seg)
  let segs = filter isVirt (M.memSegments mem)
  Map.fromList <$> traverse (mkMemSegmentBinding halloc (M.memWidth mem)) segs

stepBlocks :: forall sym arch ids
           .  (IsSymInterface sym, M.ArchConstraints arch)
           => sym
           -> ArchStepInfo arch
           -> M.Memory (M.ArchAddrWidth arch)
              -- ^ Memory image for executable
           -> Text
              -- ^ Name of executable
           -> Word64
              -- ^ Starting IP for block
           -> [M.Block arch ids]
              -- ^ List of blocks
           -> IO (C.ExecResult
                   MacawSimulatorState
                   sym
                   (C.RegEntry sym (C.StructType (CtxToCrucibleType (ArchRegContext arch)))))
stepBlocks sym sinfo mem binPath addr macawBlocks = do
  let regAssign = archRegAssignment sinfo
  let crucRegTypes = typeCtxToCrucible (fmapFC M.typeRepr regAssign)
  let macawStructRepr = C.StructRepr crucRegTypes
  halloc <- C.newHandleAllocator
  let argTypes = Ctx.empty Ctx.%> macawStructRepr
  let nm = fromString $ "macaw_0x" ++ showHex addr ""
  h <- stToIO $ C.mkHandle' halloc nm argTypes macawStructRepr
  -- Map block map to Crucible CFG
  let blockLabelMap :: Map Word64 (CR.Label RealWorld)
      blockLabelMap = Map.fromList [ (w, CR.Label (fromIntegral w))
                                   | w <- M.blockLabel <$> macawBlocks ]
  memSegmentVarMap <- stToIO $ mkMemSegmentMap halloc mem

  let genCtx = CrucGenContext { archConstraints = \x -> x
                              , macawRegAssign = regAssign
                              , regIndexMap = mkRegIndexMap regAssign (Ctx.size crucRegTypes)
                              , translateArchFn = archTranslateFn sinfo
                              , translateArchStmt = archTranslateStmt sinfo
                              , handleAlloc = halloc
                              , binaryPath = binPath
                              , macawIndexToLabelMap = blockLabelMap
                              , memSegmentMap = memSegmentVarMap
                              }
  let ps0 = initCrucPersistentState
  blockRes <- stToIO $ runStateT (runExceptT (mapM_ (addMacawBlock genCtx) macawBlocks)) ps0
  ps <-
    case blockRes of
      (Left err, _) -> fail err
      (Right _, s)  -> pure s
  -- Create control flow graph
  let rg :: CR.CFG RealWorld (MacawFunctionArgs arch) (MacawFunctionResult arch)
      rg = CR.CFG { CR.cfgHandle = h
                  , CR.cfgBlocks = Map.elems (seenBlockMap ps)
                  }
  cfg <- C.initialConfig 0 []
  let ctx :: C.SimContext MacawSimulatorState sym
      ctx = C.SimContext { C._ctxSymInterface = sym
                         , C.ctxSolverProof = \a -> a
                         , C.ctxIntrinsicTypes = MapF.empty
                         , C.simConfig = cfg
                         , C.simHandleAllocator = halloc
                         , C.printHandle = stdout
                         , C._functionBindings = createHandleMap genCtx (handleMap ps)
                         , C._cruciblePersonality = MacawSimulatorState
                         }
  -- Create the symbolic simulator state
  let s = C.initSimState ctx C.emptyGlobals C.defaultErrorHandler
  -- Define the arguments to call the Reopt CFG with.
  -- This should be a symbolic variable for each register in the architecture.
  regStruct <- regVars sym (archRegNameFn sinfo) regAssign
  let args :: C.RegMap sym (MacawFunctionArgs arch)
      args = C.RegMap (Ctx.singleton (C.RegEntry macawStructRepr regStruct))
  -- Run the symbolic simulator.
  case C.toSSA rg of
    C.SomeCFG g ->
      C.runOverrideSim s macawStructRepr $ do
        C.regValue <$> C.callCFG g args
