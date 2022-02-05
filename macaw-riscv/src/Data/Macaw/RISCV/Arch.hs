{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.RISCV.Arch
  ( -- * RISC-V functions, statements, and terminators
    RISCV
  , RISCVPrimFn(..)
  , RISCVStmt
  , RISCVTermStmt
  , riscvPrimFnHasSideEffects
  , rewriteRISCVPrimFn
  , type RISCVConstraints
  ) where

import qualified Data.Kind as K
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Rewriter as MCR
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Classes as PC
import           Data.Parameterized.NatRepr
import qualified Data.Parameterized.TraversableF as F
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Macaw.Types as MT
import qualified GRIFT.Types as G

import qualified Prettyprinter as PP

data RISCV (rv :: G.RV)

-- | Macaw-specific constraints we need for the RISC-V configuration
-- type parameter.
type RISCVConstraints rv = ( MM.MemWidth (G.RVWidth rv)
                           )

-- | RISC-V architecture-specific functions
data RISCVPrimFn (rv :: G.RV) (expr :: MT.Type -> K.Type) (tp :: MT.Type) where

  -- TODO: put reg values in here and check how many values are returned
  -- TODO: Docs
  RISCVEcall :: ( 1 <= w, MT.KnownNat w )
             => NatRepr w
             -> RISCVPrimFn rv expr (MT.BVType w)

instance FC.FunctorFC (RISCVPrimFn v) where
  fmapFC = FC.fmapFCDefault

instance FC.FoldableFC (RISCVPrimFn rv) where
  foldMapFC = FC.foldMapFCDefault

instance FC.TraversableFC (RISCVPrimFn rv) where
  traverseFC go f =
    case f of
      RISCVEcall w -> pure $ RISCVEcall w

instance MC.IsArchFn (RISCVPrimFn rv) where
  ppArchFn pp f =
    case f of
      RISCVEcall _ -> pure $ PP.pretty "riscv_ecall"

instance MT.HasRepr (RISCVPrimFn rv expr) MT.TypeRepr where
  typeRepr f =
    case f of
      RISCVEcall{} -> PC.knownRepr

rewriteRISCVPrimFn
  :: RISCVPrimFn rv (MC.Value (RISCV rv) src) tp
  -> MCR.Rewriter (RISCV rv) s src tgt (MC.Value (RISCV rv) tgt tp)
rewriteRISCVPrimFn f =
  case f of
    RISCVEcall w ->
      -- TODO: Rewrite the arguments once they're in RISCVEcall
      MCR.evalRewrittenArchFn (RISCVEcall w)

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

instance MC.IsArchTermStmt (RISCVTermStmt rv) where
  ppArchTermStmt _ _ = error "ppArchTermStmt undefined for RISCVTermStmt"

type instance MC.ArchBlockPrecond (RISCV rv) = ()

riscvPrimFnHasSideEffects :: RISCVPrimFn rv f tp -> Bool
riscvPrimFnHasSideEffects = const False -- TODO: Is this right?
