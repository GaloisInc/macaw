{-# LANGUAGE ExistentialQuantification #-}
{-# LANGUAGE RankNTypes #-}
-- | This module exports additional definitions that are required to implement
-- architecture-specific backends for macaw-symbolic.
--
-- See macaw-x86-symbolic and macaw-ppc-symbolic for examples of how to write a
-- backend.
module Data.Macaw.Symbolic.Backend (
    -- * Creating an architecture-specific backend
    --
    -- $archBackend
    CG.MacawArchStmtExtension
  , CG.CrucGen
  , PS.macawAssignToCrucM
  , CG.valueToCrucible
  , CG.evalArchStmt
  , MacawArchEvalFn(..)
  , EvalStmtFunc
    -- ** Simulator Operations
  , MO.doPtrAdd
  , MO.doPtrSub
  , MO.doPtrMux
  , MO.doPtrEq
  , MO.doPtrLt
  , MO.doPtrLeq
  , MO.doPtrAnd
  , MO.doReadMem
  , MO.doCondReadMem
  , MO.doWriteMem
  , MO.doGetGlobal
  , MO.doLookupFunctionHandle
  , MO.doPtrToBits
    -- ** Register Mapping
  , PS.RegIndexMap
  , PS.mkRegIndexMap
  , PS.IndexPair(..)
  , CG.crucArchRegTypes
    -- * Constructors
  , CG.MacawSymbolicArchFunctions(..)
  ) where

import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.LLVM.MemModel as MM
import qualified Lang.Crucible.Simulator as C
import qualified Data.Macaw.CFG.Core as M

import qualified Data.Macaw.Symbolic.CrucGen as CG
import qualified Data.Macaw.Symbolic.PersistentState as PS
import qualified Data.Macaw.Symbolic.MemOps as MO

-- | A type for an evaluator of architecture-specific statements
type EvalStmtFunc f p sym ext =
  forall rtp blocks r ctx tp'.
    f (C.RegEntry sym) tp'
    -> C.CrucibleState p sym ext rtp blocks r ctx
    -> IO (C.RegValue sym tp', C.CrucibleState p sym ext rtp blocks r ctx)

-- | Function for evaluating an architecture-specific statements
--
-- The constructor is exposed to facilitate the construction of new
-- architecture-specific backends - client code should not need to construct
-- values of this type, and instead should obtain values of this type from the
-- 'withArchEval' function.
newtype MacawArchEvalFn sym arch =
  MacawArchEvalFn (C.GlobalVar MM.Mem -> MO.GlobalMap sym (M.ArchAddrWidth arch) -> EvalStmtFunc (CG.MacawArchStmtExtension arch) (MO.MacawSimulatorState sym) sym (CG.MacawExt arch))

-- $archBackend
--
-- These are the interfaces required for implementing a translation of an
-- architecture-specific macaw backend into Crucible (e.g., see
-- macaw-x86-symbolic).
