{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.RISCV.Arch where

import qualified Data.Kind as K
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.TraversableF as F
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Macaw.Types as MT
import qualified GRIFT.Types as GT
import qualified Text.PrettyPrint.ANSI.Leijen as PP

type RISCV rv = ( MM.MemWidth (GT.RVWidth rv)
                )

-- | RISC-V architecture-specific functions
data RISCVPrimFn (rv :: GT.RV) (expr :: MT.Type -> K.Type) (tp :: MT.Type)

instance FC.FoldableFC (RISCVPrimFn rv) where
  foldMapFC _ _ = undefined

instance MC.IsArchFn (RISCVPrimFn rv) where
  ppArchFn _ _ = undefined

type instance MC.ArchFn rv = RISCVPrimFn rv

-- | RISC-V architecture-specific statements
data RISCVArchStmt (rv :: GT.RV) (expr :: MT.Type -> K.Type)

instance F.FoldableF (RISCVArchStmt rv) where
  foldMapF _ _ = undefined

instance MC.IsArchStmt (RISCVArchStmt rv) where
  ppArchStmt _ _ = undefined

type instance MC.ArchStmt rv = RISCVArchStmt rv

-- | RISC-V block termination statements
data RISCVArchTermStmt (rv :: GT.RV) ids where
  Ecall :: RISCVArchTermStmt rv ids

instance MC.PrettyF (RISCVArchTermStmt rv) where
  prettyF Ecall = PP.text "ecall"

-- The IPAlignment instance will likely need to take computations like
-- this into account (for JAL):
--   x[rd] := pc + zext(step) pc := pc +
--   sext(imm20 << 0x1)
-- But for now, we leave it as trivial.
instance MC.IPAlignment (rv :: GT.RV) where
  fromIPAligned = Just
  toIPAligned = id

type instance MC.ArchTermStmt (rv :: GT.RV) = RISCVArchTermStmt rv

type instance MC.ArchBlockPrecond (rv :: GT.RV) = ()

riscvPrimFnHasSideEffects :: RISCVPrimFn rv f tp -> Bool
riscvPrimFnHasSideEffects _ = False
