{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
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

  -- | Issue an executive call (system call)
  --
  -- This captures all of the necessary registers as inputs and outputs to
  -- enable translation to crucible.  See the x86 version for more information
  -- on this translation.
  --
  -- The NatRepr is the register width.  The remaining arguments are all of the
  -- registers that participate in the syscall protocol (on Linux).  Arguments
  -- are passed in a0-a6, while the syscall number is in a7.
  --
  -- The system call can return up to two values (in a0 and a1)
  RISCVEcall :: ( 1 <= w, MT.KnownNat w )
             => NatRepr w
             -> expr (MT.BVType w) -- a0
             -> expr (MT.BVType w) -- a1
             -> expr (MT.BVType w) -- a2
             -> expr (MT.BVType w) -- a3
             -> expr (MT.BVType w) -- a4
             -> expr (MT.BVType w) -- a5
             -> expr (MT.BVType w) -- a6
             -> expr (MT.BVType w) -- a7 (syscall number)
             -> RISCVPrimFn rv expr (MT.TupleType [MT.BVType w, MT.BVType w])

instance FC.FunctorFC (RISCVPrimFn v) where
  fmapFC = FC.fmapFCDefault

instance FC.FoldableFC (RISCVPrimFn rv) where
  foldMapFC = FC.foldMapFCDefault

instance FC.TraversableFC (RISCVPrimFn rv) where
  traverseFC go f =
    case f of
      RISCVEcall w a0 a1 a2 a3 a4 a5 a6 a7 ->
        RISCVEcall w <$> go a0 <*> go a1 <*> go a2 <*> go a3 <*> go a4 <*> go a5 <*> go a6 <*> go a7

instance MC.IsArchFn (RISCVPrimFn rv) where
  ppArchFn pp f =
    let ppSC s w a0 a1 a2 a3 a4 a5 a6 a7 = s PP.<+> PP.viaShow w PP.<+> a0 PP.<+> a1 PP.<+> a2 PP.<+> a3 PP.<+> a4 PP.<+> a5 PP.<+> a6 PP.<+> a7
    in case f of
      RISCVEcall w a0 a1 a2 a3 a4 a5 a6 a7 ->
        ppSC "riscv_ecall" w <$> pp a0 <*> pp a1 <*> pp a2 <*> pp a3 <*> pp a4 <*> pp a5 <*> pp a6 <*> pp a7

instance MT.HasRepr (RISCVPrimFn rv expr) MT.TypeRepr where
  typeRepr f =
    case f of
      RISCVEcall{} -> PC.knownRepr

rewriteRISCVPrimFn
  :: RISCVPrimFn rv (MC.Value (RISCV rv) src) tp
  -> MCR.Rewriter (RISCV rv) s src tgt (MC.Value (RISCV rv) tgt tp)
rewriteRISCVPrimFn f =
  case f of
    RISCVEcall w a0 a1 a2 a3 a4 a5 a6 a7 -> do
      tgtFn <- RISCVEcall w <$> MCR.rewriteValue a0 <*> MCR.rewriteValue a1 <*> MCR.rewriteValue a2 <*> MCR.rewriteValue a3 <*> MCR.rewriteValue a4 <*> MCR.rewriteValue a5 <*> MCR.rewriteValue a6 <*> MCR.rewriteValue a7
      MCR.evalRewrittenArchFn tgtFn

type instance MC.ArchFn (RISCV rv) = RISCVPrimFn rv

-- | RISC-V architecture-specific statements (none)
data RISCVStmt (rv :: G.RV) (expr :: MT.Type -> K.Type)

instance F.FunctorF (RISCVStmt rv) where
  fmapF _ s = case s of {}

instance F.FoldableF (RISCVStmt rv) where
  foldMapF _ s = case s of {}

instance F.TraversableF (RISCVStmt rv) where
  traverseF _ s = pure (case s of {})

instance MC.IsArchStmt (RISCVStmt rv) where
  ppArchStmt _ s = case s of {}

type instance MC.ArchStmt (RISCV rv) = RISCVStmt rv

-- | RISC-V block termination statements (none)
data RISCVTermStmt (rv :: G.RV) (f :: MT.Type -> K.Type)

instance F.FunctorF (RISCVTermStmt rv) where
  fmapF _ s = case s of {}

instance F.FoldableF (RISCVTermStmt rv) where
  foldMapF _ s = case s of {}

instance F.TraversableF (RISCVTermStmt rv) where
  traverseF _ s = pure (case s of {})

instance MC.PrettyF (RISCVTermStmt rv) where
  prettyF s = case s of {}

-- The IPAlignment instance will likely need to take computations like
-- this into account (for JAL):
--   x[rd] := pc + zext(step) pc := pc +
--   sext(imm20 << 0x1)
-- But for now, we leave it as trivial.
instance MC.IPAlignment (RISCV rv) where
  fromIPAligned = Just
  toIPAligned = id

type instance MC.ArchTermStmt (RISCV rv) = RISCVTermStmt rv

instance MC.IsArchTermStmt (RISCVTermStmt rv) where
  ppArchTermStmt _ s = case s of {}

type instance MC.ArchBlockPrecond (RISCV rv) = ()

-- | The existing architecture specific functions have no side effects
riscvPrimFnHasSideEffects :: RISCVPrimFn rv f tp -> Bool
riscvPrimFnHasSideEffects = const False
