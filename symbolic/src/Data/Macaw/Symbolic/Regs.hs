{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}

module Data.Macaw.Symbolic.Regs
  ( simStateRegs
  , execStateRegs
  ) where

import Control.Applicative ((<|>))
import Control.Lens qualified as Lens
import Data.Macaw.Symbolic qualified as M
import Data.Parameterized.Context qualified as Ctx
import Data.Type.Equality ((:~:)(Refl), testEquality)
import Lang.Crucible.CFG.Core qualified as C
import Lang.Crucible.Simulator.CallFrame qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import Lang.Crucible.Simulator.RegMap qualified as C

-- | Helper, not exported
mostRecentValOfTypeInAssignment ::
  C.TypeRepr t ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  Maybe (C.RegValue sym t)
mostRecentValOfTypeInAssignment ty =
  \case
    Ctx.Empty -> Nothing
    ctx Ctx.:> C.RegEntry ty' v ->
      case testEquality ty ty' of
        Just Refl -> Just v
        Nothing -> mostRecentValOfTypeInAssignment ty ctx

-- | Helper, not exported
mostRecentValOfTypeInRegMap ::
  C.TypeRepr t ->
  C.RegMap sym ctx ->
  Maybe (C.RegValue sym t)
mostRecentValOfTypeInRegMap ty =
  mostRecentValOfTypeInAssignment ty . C.regMap

-- | Helper, not exported
mostRecentValOfTypeInFrames ::
  C.TypeRepr t ->
  [C.SomeFrame (C.SimFrame sym ext)] ->
  Maybe (C.RegValue sym t)
mostRecentValOfTypeInFrames ty =
  \case
    [] -> Nothing
    (C.SomeFrame f : fs) ->
      case f of
        C.OF ovFrame ->
          mostRecentValOfTypeInRegMap ty (ovFrame Lens.^. C.overrideRegMap) <|>
            mostRecentValOfTypeInFrames ty fs
        C.MF callFrame ->
          mostRecentValOfTypeInRegMap ty (callFrame Lens.^. C.frameRegs) <|>
            mostRecentValOfTypeInFrames ty fs
        C.RF {} -> mostRecentValOfTypeInFrames ty fs

-- | Helper, not exported
mostRecentValOfTypeInSimState ::
  C.SimState p sym ext r f args ->
  C.TypeRepr t ->
  Maybe (C.RegValue sym t)
mostRecentValOfTypeInSimState simState ty =
  let frs = simState Lens.^. C.stateTree . Lens.to C.activeFrames in
  mostRecentValOfTypeInFrames ty frs

-- | Get the most recently-defined value of type @'M.ArchRegStruct' arch@ in
-- a 'C.SimState'.
simStateRegs ::
  M.MacawSymbolicArchFunctions arch ->
  C.SimState p sym ext r f args ->
  Maybe (C.RegValue sym (M.ArchRegStruct arch))
simStateRegs archFns simState =
  let regType = C.StructRepr (M.crucArchRegTypes archFns) in
  mostRecentValOfTypeInSimState simState regType

-- | Get the most recently-defined value of type @'M.ArchRegStruct' arch@ in
-- an 'C.ExecState'.
execStateRegs ::
  M.MacawSymbolicArchFunctions arch ->
  C.ExecState p sym ext r ->
  Maybe (C.RegValue sym (M.ArchRegStruct arch))
execStateRegs archFns execState = do
  C.SomeSimState simState <- C.execStateSimState execState
  simStateRegs archFns simState
