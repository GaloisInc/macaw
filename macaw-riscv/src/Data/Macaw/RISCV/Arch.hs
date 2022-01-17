{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.RISCV.Arch
  ( -- * RISC-V functions, statements, and terminators
    -- | There are none at this time.
    RISCV
  , RISCVPrimFn
  , RISCVStmt
  , RISCVTermStmt
  , riscvPrimFnHasSideEffects
  , type RISCVConstraints
  ) where

import qualified Data.Kind as K
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.TraversableF as F
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Macaw.Types as MT
import qualified GRIFT.Types as G

data RISCV (rv :: G.RV)

-- | Macaw-specific constraints we need for the RISC-V configuration
-- type parameter.
type RISCVConstraints rv = ( MM.MemWidth (G.RVWidth rv)
                           )

-- | RISC-V architecture-specific functions (none)
data RISCVPrimFn (rv :: G.RV) (expr :: MT.Type -> K.Type) (tp :: MT.Type)

instance FC.FoldableFC (RISCVPrimFn rv) where
  foldMapFC _ _ = error "foldMapFC undefined for RISCVPrimFn"

instance MC.IsArchFn (RISCVPrimFn rv) where
  ppArchFn _ _ = error "ppArchFn undefined for RISCVPrimFn"

type instance MC.ArchFn (RISCV rv) = RISCVPrimFn rv

-- | RISC-V architecture-specific statements (none)
data RISCVStmt (rv :: G.RV) (expr :: MT.Type -> K.Type)

instance F.FoldableF (RISCVStmt rv) where
  foldMapF _ _ = error "foldMapF undefined for RISCVStmt"

instance MC.IsArchStmt (RISCVStmt rv) where
  ppArchStmt _ _ = error "ppArchStmt undefined for RISCVStmt"

type instance MC.ArchStmt (RISCV rv) = RISCVStmt rv

-- | RISC-V block termination statements (none)
data RISCVTermStmt (rv :: G.RV) (f :: MT.Type -> K.Type)

instance MC.PrettyF (RISCVTermStmt rv) where
  prettyF = error "PrettyF undefined for RISCVTermStmt"

-- The IPAlignment instance will likely need to take computations like
-- this into account (for JAL):
--   x[rd] := pc + zext(step) pc := pc +
--   sext(imm20 << 0x1)
-- But for now, we leave it as trivial.
-- | This is an orphan instance because we are reusing the 'G.RV' type
-- from GRIFT.
instance MC.IPAlignment (RISCV rv) where
  fromIPAligned = Just
  toIPAligned = id

type instance MC.ArchTermStmt (RISCV rv) = RISCVTermStmt rv

type instance MC.ArchBlockPrecond (RISCV rv) = ()

riscvPrimFnHasSideEffects :: RISCVPrimFn rv f tp -> Bool
riscvPrimFnHasSideEffects _ = error "riscvPrimFnHasSideEffects undefined for RISCVPrimFn"
