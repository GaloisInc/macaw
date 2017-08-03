{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.Symbolic
  ( stepBlocks
  ) where

import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableFC
import           Data.String
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
import qualified Data.Macaw.Types as M

import Data.Macaw.Symbolic.App

data ReoptSimulatorState sym = ReoptSimulatorState



-- Return the types associated with a register assignment.
regTypes :: Ctx.Assignment M.TypeRepr ctx
         -> Ctx.Assignment C.TypeRepr (CtxToCrucibleType ctx)
regTypes a =
  case Ctx.view a of
    Ctx.AssignEmpty -> Ctx.empty
    Ctx.AssignExtend b tp -> regTypes b Ctx.%> typeToCrucible tp

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

translateBlock :: CrucGenContext arch ids s
               -> M.Block arch ids
               -> StateT (CrucPersistentState arch ids s) (ST s) ()
translateBlock = undefined
{-
translateBlock ctx blockMap idx ip = do
  s <- get
  mr <- lift $ runExceptT (mkCrucibleBlock ctx undefined s b)
  case mr of
    Left err ->
      fail err
    Right r -> do
      undefined r
-}

translateBlocks :: CrucGenContext arch ids s
                -> Map Word64 (M.Block arch ids)
                -> ST s (CrucGenHandles arch, [CR.Block s (MacawFunctionResult arch)])
translateBlocks genCtx l = do
  let ps0 = CrucPersistentState
          { handleMap = undefined
          , valueCount = 0
          , assignValueMap = MapF.empty
          , seenBlockMap = Map.empty
          }
  ps <- execStateT (mapM_ (translateBlock genCtx) (Map.elems l)) ps0
  pure (handleMap ps, Map.elems (seenBlockMap ps))

createHandleMap :: CrucGenHandles arch -> C.FunctionBindings ReoptSimulatorState sym
createHandleMap = undefined

stepBlocks :: forall sym arch ids
           .  (IsSymInterface sym, M.ArchConstraints arch)
           => sym
           -> (forall tp . M.ArchReg arch tp -> SolverSymbol)
           -> Ctx.Assignment (M.ArchReg arch) (ArchRegContext arch)
           -> Word64
              -- ^ Starting IP for block
           -> Map Word64 (M.Block arch ids)
              -- ^ Map from block indices to block
           -> IO (C.ExecResult
                   ReoptSimulatorState
                   sym
                   (C.RegEntry sym (C.StructType (CtxToCrucibleType (ArchRegContext arch)))))
stepBlocks sym nameFn regAssign addr macawBlockMap = do
  let macawStructRepr = C.StructRepr (regTypes (fmapFC M.typeRepr regAssign))
  halloc <- C.newHandleAllocator
  let argTypes = Ctx.empty Ctx.%> macawStructRepr
  let nm = fromString $ "macaw_0x" ++ showHex addr ""
  h <- stToIO $ C.mkHandle' halloc nm argTypes macawStructRepr
  -- Map block map to Crucible CFG
  let blockLabelMap :: Map Word64 (CR.Label RealWorld)
      blockLabelMap = Map.fromList [ (w, CR.Label (fromIntegral w)) | w <- Map.keys macawBlockMap ]
  let genCtx = CrucGenContext { archConstraints = \x -> x
                              , translateArchFn = undefined
                              , translateArchStmt = undefined
                              , handleAlloc = halloc
                              , binaryPath = undefined
                              , macawIndexToLabelMap = blockLabelMap
                              , memSegmentMap = undefined
                              , regValueMap = undefined
                              , syscallHandle = undefined
                              }
  (hndls, blks) <- stToIO $ translateBlocks genCtx  macawBlockMap
  -- Create control flow graph
  let rg :: CR.CFG RealWorld (MacawFunctionArgs arch) (MacawFunctionResult arch)
      rg = CR.CFG { CR.cfgHandle = h
                  , CR.cfgBlocks = blks
                  }
  cfg <- C.initialConfig 0 []
  let ctx :: C.SimContext ReoptSimulatorState sym
      ctx = C.SimContext { C._ctxSymInterface = sym
                         , C.ctxSolverProof = \a -> a
                         , C.ctxIntrinsicTypes = MapF.empty
                         , C.simConfig = cfg
                         , C.simHandleAllocator = halloc
                         , C.printHandle = stdout
                         , C._functionBindings = createHandleMap hndls
                         , C._cruciblePersonality = ReoptSimulatorState
                         }
  -- Create the symbolic simulator state
  let s = C.initSimState ctx C.emptyGlobals C.defaultErrorHandler
  -- Define the arguments to call the Reopt CFG with.
  -- This should be a symbolic variable for each register in the architecture.
  regStruct <- regVars sym nameFn regAssign
  let args :: C.RegMap sym (MacawFunctionArgs arch)
      args = C.RegMap (Ctx.singleton (C.RegEntry macawStructRepr regStruct))
  -- Run the symbolic simulator.
  case C.toSSA rg of
    C.SomeCFG g ->
      C.runOverrideSim s macawStructRepr $ do
        C.regValue <$> C.callCFG g args
