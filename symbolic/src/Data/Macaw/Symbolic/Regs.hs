{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE RankNTypes #-}

module Data.Macaw.Symbolic.Regs
  ( simStateRegs
  , execStateRegs
  , setSimStateRegs
  , setExecStateRegs
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

-----------------------------------------------------------
-- Getters

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

-----------------------------------------------------------
-- Setters

-- | Helper, not exported
setMostRecentValOfTypeInAssignment ::
  C.RegEntry sym t ->
  Ctx.Assignment (C.RegEntry sym) ctx ->
  Ctx.Assignment (C.RegEntry sym) ctx
setMostRecentValOfTypeInAssignment v@(C.RegEntry ty _) =
  \case
    Ctx.Empty -> Ctx.Empty
    ctx Ctx.:> v'@(C.RegEntry ty' _) ->
      case testEquality ty ty' of
        Just Refl -> ctx Ctx.:> v
        Nothing -> setMostRecentValOfTypeInAssignment v ctx Ctx.:> v'

-- | Helper, not exported
setMostRecentValOfTypeInRegMap ::
  C.RegEntry sym t ->
  C.RegMap sym ctx ->
  C.RegMap sym ctx
setMostRecentValOfTypeInRegMap v =
  C.RegMap . setMostRecentValOfTypeInAssignment v . C.regMap

-- | Helper, not exported
setMostRecentValOfTypeInFrame ::
  C.RegEntry sym t ->
  C.SimFrame sym ext ret args ->
  C.SimFrame sym ext ret args
setMostRecentValOfTypeInFrame v =
  \case
    C.OF ovFrame ->
      C.OF (ovFrame Lens.& C.overrideRegMap Lens.%~ setMostRecentValOfTypeInRegMap v)
    C.MF callFrame ->
      C.MF (callFrame Lens.& C.frameRegs Lens.%~ setMostRecentValOfTypeInRegMap v)
    rf@C.RF {} -> rf

-- | Helper, not exported
setMostRecentValOfTypeInSimState ::
  C.RegEntry sym t ->
  C.SimState p sym ext r f args ->
  C.SimState p sym ext r f args
setMostRecentValOfTypeInSimState v simState =
  simState Lens.& C.stateTree Lens.%~
    \(C.ActiveTree ctx ar) ->
      C.ActiveTree ctx (ar Lens.& C.partialValue . C.gpValue Lens.%~ setMostRecentValOfTypeInFrame v)

-- | Set the most recently-defined value of type @'M.ArchRegStruct' arch@ in the
-- top frame of a 'C.SimState'.
setSimStateRegs ::
  proxy arch ->
  C.RegEntry sym (M.ArchRegStruct arch) ->
  C.SimState p sym ext r f args ->
  C.SimState p sym ext r f args
setSimStateRegs _proxy v simState =
  setMostRecentValOfTypeInSimState v simState

-- | Helper, not exported
modifyExecStateSimState ::
  (forall f args. C.SimState p sym ext r f args -> C.SimState p sym ext r f args) ->
  C.ExecState p sym ext r ->
  C.ExecState p sym ext r
modifyExecStateSimState f es =
  case es of
    C.ResultState _                  -> es
    C.AbortState x ss                -> C.AbortState x (f ss)
    C.UnwindCallState x y ss         -> C.UnwindCallState x y (f ss)
    C.CallState x y ss               -> C.CallState x y (f ss)
    C.TailCallState x y ss           -> C.TailCallState x y (f ss)
    C.ReturnState x y z ss           -> C.ReturnState x y z (f ss)
    C.ControlTransferState x ss      -> C.ControlTransferState x (f ss)
    C.RunningState x ss              -> C.RunningState x (f ss)
    C.SymbolicBranchState x y z w ss -> C.SymbolicBranchState x y z w (f ss)
    C.OverrideState x ss             -> C.OverrideState x (f ss)
    C.BranchMergeState x ss          -> C.BranchMergeState x (f ss)
    C.InitialState _ _ _ _ _         -> es

-- | Set the most recently-defined value of type @'M.ArchRegStruct' arch@ in the
-- top frame of an 'C.ExecState'.
setExecStateRegs ::
  proxy arch ->
  C.RegEntry sym (M.ArchRegStruct arch) ->
  C.ExecState p sym ext r ->
  C.ExecState p sym ext r
setExecStateRegs proxy v =
  modifyExecStateSimState (setSimStateRegs proxy v)
