{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.RISCV (
  -- * Macaw configurations
  riscv_info,
  -- * Type-level tags
  -- * PPC Types
  ) where

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.DemandSet as MD
import qualified Data.Macaw.Architecture.Info as MI
import qualified GRIFT.Types as G

import Data.Macaw.RISCV.Arch
import Data.Macaw.RISCV.Disassemble (riscvDisassembleFn)
import Data.Macaw.RISCV.Eval
import Data.Macaw.RISCV.Identify
import Data.Macaw.RISCV.RISCVReg

riscvDemandContext :: MD.DemandContext (rv :: G.RV)
riscvDemandContext = MD.DemandContext
  { MD.demandConstraints = \a -> a
  , MD.archFnHasSideEffects = riscvPrimFnHasSideEffects
  }

riscv_info :: RISCV rv => G.RVRepr rv -> MI.ArchitectureInfo rv
riscv_info rvRepr = G.withRV rvRepr $ MI.ArchitectureInfo
  { MI.withArchConstraints = \x -> x
  , MI.archAddrWidth = riscvAddrWidth rvRepr
  , MI.archEndianness = MC.LittleEndian
  , MI.extractBlockPrecond = \_ _ -> Right ()
  , MI.initialBlockRegs = \startIP _ -> riscvInitialBlockRegs rvRepr startIP
  , MI.disassembleFn = riscvDisassembleFn rvRepr
  , MI.mkInitialAbsState = riscvInitialAbsState rvRepr
  , MI.absEvalArchFn = \_ _ -> undefined
  , MI.absEvalArchStmt = \_ _ -> undefined
  , MI.identifyCall = riscvIdentifyCall rvRepr
  , MI.archCallParams = riscvCallParams
  , MI.checkForReturnAddr = riscvCheckForReturnAddr rvRepr
  , MI.identifyReturn = riscvIdentifyReturn rvRepr
  , MI.rewriteArchFn = \_ -> undefined
  , MI.rewriteArchStmt = \_ -> undefined
  , MI.rewriteArchTermStmt = \_ -> undefined
  , MI.archDemandContext = riscvDemandContext
  , MI.postArchTermStmtAbsState = \_ _ _ _ _ -> undefined
  }
