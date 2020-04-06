{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
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
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.Memory as MM
import qualified GRIFT.Types as GT

import Data.Macaw.RISCV.Arch ()
import Data.Macaw.RISCV.RISCVReg

riscv_info :: RISCV rv => GT.RVRepr rv -> MI.ArchitectureInfo rv
riscv_info rvRepr = MI.ArchitectureInfo
  { MI.withArchConstraints = \x -> x
  , MI.archAddrWidth = riscvAddrWidth rvRepr
  , MI.archEndianness = MC.LittleEndian
  , MI.extractBlockPrecond = \_ _ -> undefined
  , MI.initialBlockRegs = \_ _ -> undefined
  , MI.disassembleFn = \_ _ _ _ -> undefined
  , MI.mkInitialAbsState = \_ _ -> undefined
  , MI.absEvalArchFn = \_ _ -> undefined
  , MI.absEvalArchStmt = \_ _ -> undefined
  , MI.identifyCall = \_ _ _ -> undefined
  , MI.archCallParams = undefined
  , MI.checkForReturnAddr = \_ _ -> undefined
  , MI.identifyReturn = \_ _ _ -> undefined
  , MI.rewriteArchFn = \_ -> undefined
  , MI.rewriteArchStmt = \_ -> undefined
  , MI.rewriteArchTermStmt = \_ -> undefined
  , MI.archDemandContext = undefined
  , MI.postArchTermStmtAbsState = \_ _ _ _ _ -> undefined
  }

riscvAddrWidth :: GT.RVRepr rv -> MM.AddrWidthRepr (MC.RegAddrWidth (MC.ArchReg rv))
riscvAddrWidth rvRepr = case GT.rvBaseArch rvRepr of
  GT.RV32Repr -> MM.Addr32
  GT.RV64Repr -> MM.Addr64
  GT.RV128Repr -> error "RV128 not supported"
