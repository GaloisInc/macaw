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

import qualified Data.Macaw.Architecture.Info as MI
import qualified GRIFT.Types as GT

import Data.Macaw.RISCV.RISCVReg

riscv_info :: RISCV rv => GT.RVRepr rv -> MI.ArchitectureInfo rv
riscv_info _ = MI.ArchitectureInfo
  { MI.withArchConstraints = \_ -> undefined -- \x -> x
  , MI.archAddrWidth = undefined
  , MI.archEndianness = undefined
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
