{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.Symbolic
  ( stepBlocks
  ) where

import           Control.Monad.ST
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Ctx
import qualified Data.Parameterized.Map as MapF
import qualified Data.Set as Set
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

data ReoptSimulatorState sym = ReoptSimulatorState

type family ArchRegContext (arch :: *) :: Ctx C.CrucibleType

type ArchRegStruct (arch :: *) = C.StructType (ArchRegContext arch)

type MacawFunctionArgs arch = EmptyCtx ::> ArchRegStruct arch
type MacawFunctionResult arch = ArchRegStruct arch

translateBlock :: Map Word64 (CR.Label s)
                  -- ^ Map from block indices to the associated label.
               -> M.Block arch ids
               -> Either String (CR.Block s (MacawFunctionResult arch))
translateBlock idMap b = do
  let idx = M.blockLabel b
  lbl <-
    case Map.lookup idx idMap of
      Just lbl -> Right (CR.LabelID lbl)
      Nothing -> Left $ "Internal: Could not find block with index " ++ show idx
  let stmts = undefined
      term = undefined
  pure $ CR.mkBlock lbl Set.empty stmts term

stepBlocks :: forall sym arch ids
           .  IsSymInterface sym
           => sym
           -> Ctx.Assignment C.TypeRepr (ArchRegContext arch)
           -> Word64
           -> Map Word64 (M.Block arch ids)
              -- ^ Map from block indices to block
           -> IO (C.ExecResult ReoptSimulatorState sym (C.RegEntry sym (C.StructType (ArchRegContext arch))))
stepBlocks sym regTypes addr macawBlockMap = do
  let macawStructRepr = C.StructRepr regTypes
  halloc <- C.newHandleAllocator
  let argTypes = Ctx.empty Ctx.%> macawStructRepr
  let nm = fromString $ "macaw_0x" ++ showHex addr ""
  h <- stToIO $ C.mkHandle' halloc nm argTypes macawStructRepr
  -- Map block map to Crucible CFG
  let blockLabelMap :: Map Word64 (CR.Label ())
      blockLabelMap = Map.fromList [ (w, CR.Label (fromIntegral w)) | w <- Map.keys macawBlockMap ]
  let Right blks = traverse (translateBlock blockLabelMap) $ Map.elems macawBlockMap
  -- Create control flow graph
  let rg :: CR.CFG () (MacawFunctionArgs arch) (MacawFunctionResult arch)
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
                         , C._functionBindings = C.emptyHandleMap
                         , C._cruciblePersonality = ReoptSimulatorState
                         }
  -- Create the symbolic simulator state
  let s = C.initSimState ctx C.emptyGlobals C.defaultErrorHandler
  -- Define the arguments to call the Reopt CFG with.
  -- This should be a symbolic variable for each register in the architecture.
  let args :: C.RegMap sym (MacawFunctionArgs arch)
      args = undefined
  -- Run the symbolic simulator.
  case C.toSSA rg of
    C.SomeCFG g ->
      C.runOverrideSim s macawStructRepr $ do
        C.regValue <$> C.callCFG g args
