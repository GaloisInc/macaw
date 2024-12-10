{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | 'LCSC.ParserHooks' for parsing macaw-riscv-symbolic CFGs.
module Data.Macaw.RISCV.Symbolic.Syntax
  ( riscvParserHooks
  , riscv32ParserHooks
  , riscv64ParserHooks
    -- * Types
  , riscvTypeParser
    -- * Operations
  , parseRegs
  , parseReg
  , riscvAtomParser
  ) where

import Control.Applicative ( empty )
import Control.Monad qualified as Monad
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State.Strict (MonadState)
import Control.Monad.Writer.Strict (MonadWriter)
import Data.Text qualified as Text

import Data.Macaw.Symbolic qualified as DMS
import Data.Macaw.RISCV qualified as DMR
import Data.Macaw.RISCV.Symbolic qualified as DMRS
import Data.Macaw.RISCV.Symbolic.Regs qualified as DMRR
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(..))
import GRIFT.Types qualified as G
import Lang.Crucible.CFG.Expr as Expr
import Lang.Crucible.CFG.Reg (Atom, Stmt)
import Lang.Crucible.CFG.Reg qualified as Reg
import Lang.Crucible.Syntax.Atoms qualified as LCSA
import Lang.Crucible.Syntax.Concrete qualified as LCSC
import Lang.Crucible.Syntax.Monad qualified as LCSM
import Lang.Crucible.Types qualified as LCT
import What4.ProgramLoc (Posd(..))

-- | Parser hooks for macaw-riscv-symbolic CFGs
riscvParserHooks ::
  (G.KnownRV rv, DMR.RISCVConstraints rv) =>
  G.RVRepr rv ->
  LCSC.ParserHooks ext
riscvParserHooks v =
  LCSC.ParserHooks
  { LCSC.extensionTypeParser = riscvTypeParser v
  , LCSC.extensionParser = riscvAtomParser v
  }

-- | 'riscvParserHooks' instantiated to RISCV32.
riscv32ParserHooks :: LCSC.ParserHooks ext
riscv32ParserHooks = riscvParserHooks G.rv32GCRepr

-- | 'riscvParserHooks' instantiated to RISCV64.
riscv64ParserHooks :: LCSC.ParserHooks ext
riscv64ParserHooks = riscvParserHooks G.rv64GCRepr

---------------------------------------------------------------------
-- Types

-- Helper, not exported
namedAtom :: LCSM.MonadSyntax LCSA.Atomic m => Text.Text -> m ()
namedAtom expectName = do
  name <- LCSC.atomName
  Monad.unless (name == LCSA.AtomName expectName) LCSM.cut

-- Helper, not exported
riscvRegTypes ::
  forall rv.
  (G.KnownRV rv, DMR.RISCVConstraints rv) =>
  G.RVRepr rv ->
  Ctx.Assignment LCT.TypeRepr (DMS.MacawCrucibleRegTypes (DMR.RISCV rv))
riscvRegTypes _ = DMS.crucArchRegTypes (DMRS.riscvMacawSymbolicFns @rv)

-- Helper, not exported
riscvRegStructType ::
  (G.KnownRV rv, DMR.RISCVConstraints rv) =>
  G.RVRepr rv ->
  LCT.TypeRepr (DMS.ArchRegStruct (DMR.RISCV rv))
riscvRegStructType rv = LCT.StructRepr (riscvRegTypes rv)

-- Helper, not exported
riscvRegsName :: G.RVRepr rv -> Text.Text
riscvRegsName (G.RVRepr baseArch _) =
  case baseArch of
    G.RV32Repr -> "RISCV32Regs"
    G.RV64Repr -> "RISCV64Regs"
    G.RV128Repr -> error "riscvRegsName: RV128 not yet supported"

-- | Parser for type extensions to Crucible syntax
riscvTypeParser ::
  forall rv m.
  ( LCSM.MonadSyntax LCSA.Atomic m
  , G.KnownRV rv
  , DMR.RISCVConstraints rv
  ) =>
  G.RVRepr rv ->
  m (Some LCT.TypeRepr)
riscvTypeParser rv = do
  namedAtom (riscvRegsName rv)
  pure (Some (riscvRegStructType rv))

---------------------------------------------------------------------
-- Operations

parseRegs ::
  ( LCSM.MonadSyntax LCSA.Atomic m
  , MonadIO m
  , MonadState (LCSC.SyntaxState s) m
  , MonadWriter [Posd (Stmt ext s)] m
  , IsSyntaxExtension ext
  , ?parserHooks :: LCSC.ParserHooks ext
  , G.KnownRV rv
  , DMR.RISCVConstraints rv
  ) =>
  G.RVRepr rv ->
  m (Atom s (DMS.ArchRegStruct (DMR.RISCV rv)))
parseRegs rv =
  LCSM.describe "a struct of RISC-V register values" $ do
    assign <- LCSC.operands (Ctx.Empty Ctx.:> riscvRegStructType rv)
    pure (assign Ctx.! Ctx.baseIndex)

parseReg ::
  forall rv m.
  LCSM.MonadSyntax LCSA.Atomic m =>
  G.RVRepr rv ->
  m (Some (Ctx.Index (DMS.MacawCrucibleRegTypes (DMR.RISCV rv))))
parseReg _ =
  LCSM.describe "a RISC-V register" $ do
    name <- LCSC.atomName
    case name of
      LCSA.AtomName "pc" -> pure (Some (DMRR.pc @rv))
      LCSA.AtomName "ra" -> pure (Some (DMRR.ra @rv))
      LCSA.AtomName "sp" -> pure (Some (DMRR.sp @rv))
      LCSA.AtomName "gp" -> pure (Some (DMRR.gp @rv))
      LCSA.AtomName "tp" -> pure (Some (DMRR.tp @rv))
      LCSA.AtomName "t0" -> pure (Some (DMRR.t0 @rv))
      LCSA.AtomName "t1" -> pure (Some (DMRR.t1 @rv))
      LCSA.AtomName "t2" -> pure (Some (DMRR.t2 @rv))
      LCSA.AtomName "s0" -> pure (Some (DMRR.s0 @rv))
      LCSA.AtomName "s1" -> pure (Some (DMRR.s1 @rv))
      LCSA.AtomName "a0" -> pure (Some (DMRR.a0 @rv))
      LCSA.AtomName "a1" -> pure (Some (DMRR.a1 @rv))
      LCSA.AtomName "a2" -> pure (Some (DMRR.a2 @rv))
      LCSA.AtomName "a3" -> pure (Some (DMRR.a3 @rv))
      LCSA.AtomName "a4" -> pure (Some (DMRR.a4 @rv))
      LCSA.AtomName "a5" -> pure (Some (DMRR.a5 @rv))
      LCSA.AtomName "a6" -> pure (Some (DMRR.a6 @rv))
      LCSA.AtomName "a7" -> pure (Some (DMRR.a7 @rv))
      LCSA.AtomName "s2" -> pure (Some (DMRR.s2 @rv))
      LCSA.AtomName "s3" -> pure (Some (DMRR.s3 @rv))
      LCSA.AtomName "s4" -> pure (Some (DMRR.s4 @rv))
      LCSA.AtomName "s5" -> pure (Some (DMRR.s5 @rv))
      LCSA.AtomName "s6" -> pure (Some (DMRR.s6 @rv))
      LCSA.AtomName "s7" -> pure (Some (DMRR.s7 @rv))
      LCSA.AtomName "s8" -> pure (Some (DMRR.s8 @rv))
      LCSA.AtomName "s9" -> pure (Some (DMRR.s9 @rv))
      LCSA.AtomName "s10" -> pure (Some (DMRR.s10 @rv))
      LCSA.AtomName "s11" -> pure (Some (DMRR.s11 @rv))
      LCSA.AtomName "t3" -> pure (Some (DMRR.t3 @rv))
      LCSA.AtomName "t4" -> pure (Some (DMRR.t4 @rv))
      LCSA.AtomName "t5" -> pure (Some (DMRR.t5 @rv))
      LCSA.AtomName "t6" -> pure (Some (DMRR.t6 @rv))
      LCSA.AtomName "x1" -> pure (Some (DMRR.x1 @rv))
      LCSA.AtomName "x2" -> pure (Some (DMRR.x2 @rv))
      LCSA.AtomName "x3" -> pure (Some (DMRR.x3 @rv))
      LCSA.AtomName "x4" -> pure (Some (DMRR.x4 @rv))
      LCSA.AtomName "x5" -> pure (Some (DMRR.x5 @rv))
      LCSA.AtomName "x6" -> pure (Some (DMRR.x6 @rv))
      LCSA.AtomName "x7" -> pure (Some (DMRR.x7 @rv))
      LCSA.AtomName "x8" -> pure (Some (DMRR.x8 @rv))
      LCSA.AtomName "x9" -> pure (Some (DMRR.x9 @rv))
      LCSA.AtomName "x10" -> pure (Some (DMRR.x10 @rv))
      LCSA.AtomName "x11" -> pure (Some (DMRR.x11 @rv))
      LCSA.AtomName "x12" -> pure (Some (DMRR.x12 @rv))
      LCSA.AtomName "x13" -> pure (Some (DMRR.x13 @rv))
      LCSA.AtomName "x14" -> pure (Some (DMRR.x14 @rv))
      LCSA.AtomName "x15" -> pure (Some (DMRR.x15 @rv))
      LCSA.AtomName "x16" -> pure (Some (DMRR.x16 @rv))
      LCSA.AtomName "x17" -> pure (Some (DMRR.x17 @rv))
      LCSA.AtomName "x18" -> pure (Some (DMRR.x18 @rv))
      LCSA.AtomName "x19" -> pure (Some (DMRR.x19 @rv))
      LCSA.AtomName "x20" -> pure (Some (DMRR.x20 @rv))
      LCSA.AtomName "x21" -> pure (Some (DMRR.x21 @rv))
      LCSA.AtomName "x22" -> pure (Some (DMRR.x22 @rv))
      LCSA.AtomName "x23" -> pure (Some (DMRR.x23 @rv))
      LCSA.AtomName "x24" -> pure (Some (DMRR.x24 @rv))
      LCSA.AtomName "x25" -> pure (Some (DMRR.x25 @rv))
      LCSA.AtomName "x26" -> pure (Some (DMRR.x26 @rv))
      LCSA.AtomName "x27" -> pure (Some (DMRR.x27 @rv))
      LCSA.AtomName "x28" -> pure (Some (DMRR.x28 @rv))
      LCSA.AtomName "x29" -> pure (Some (DMRR.x29 @rv))
      LCSA.AtomName "x30" -> pure (Some (DMRR.x30 @rv))
      LCSA.AtomName "x31" -> pure (Some (DMRR.x31 @rv))
      LCSA.AtomName "ft0" -> pure (Some (DMRR.ft0 @rv))
      LCSA.AtomName "ft1" -> pure (Some (DMRR.ft1 @rv))
      LCSA.AtomName "ft2" -> pure (Some (DMRR.ft2 @rv))
      LCSA.AtomName "ft3" -> pure (Some (DMRR.ft3 @rv))
      LCSA.AtomName "ft4" -> pure (Some (DMRR.ft4 @rv))
      LCSA.AtomName "ft5" -> pure (Some (DMRR.ft5 @rv))
      LCSA.AtomName "ft6" -> pure (Some (DMRR.ft6 @rv))
      LCSA.AtomName "ft7" -> pure (Some (DMRR.ft7 @rv))
      LCSA.AtomName "fs0" -> pure (Some (DMRR.fs0 @rv))
      LCSA.AtomName "fs1" -> pure (Some (DMRR.fs1 @rv))
      LCSA.AtomName "fa0" -> pure (Some (DMRR.fa0 @rv))
      LCSA.AtomName "fa1" -> pure (Some (DMRR.fa1 @rv))
      LCSA.AtomName "fa2" -> pure (Some (DMRR.fa2 @rv))
      LCSA.AtomName "fa3" -> pure (Some (DMRR.fa3 @rv))
      LCSA.AtomName "fa4" -> pure (Some (DMRR.fa4 @rv))
      LCSA.AtomName "fa5" -> pure (Some (DMRR.fa5 @rv))
      LCSA.AtomName "fa6" -> pure (Some (DMRR.fa6 @rv))
      LCSA.AtomName "fa7" -> pure (Some (DMRR.fa7 @rv))
      LCSA.AtomName "fs2" -> pure (Some (DMRR.fs2 @rv))
      LCSA.AtomName "fs3" -> pure (Some (DMRR.fs3 @rv))
      LCSA.AtomName "fs4" -> pure (Some (DMRR.fs4 @rv))
      LCSA.AtomName "fs5" -> pure (Some (DMRR.fs5 @rv))
      LCSA.AtomName "fs6" -> pure (Some (DMRR.fs6 @rv))
      LCSA.AtomName "fs7" -> pure (Some (DMRR.fs7 @rv))
      LCSA.AtomName "fs8" -> pure (Some (DMRR.fs8 @rv))
      LCSA.AtomName "fs9" -> pure (Some (DMRR.fs9 @rv))
      LCSA.AtomName "fs10" -> pure (Some (DMRR.fs10 @rv))
      LCSA.AtomName "fs11" -> pure (Some (DMRR.fs11 @rv))
      LCSA.AtomName "ft8" -> pure (Some (DMRR.ft8 @rv))
      LCSA.AtomName "ft9" -> pure (Some (DMRR.ft9 @rv))
      LCSA.AtomName "ft10" -> pure (Some (DMRR.ft10 @rv))
      LCSA.AtomName "ft11" -> pure (Some (DMRR.ft11 @rv))
      LCSA.AtomName "f0" -> pure (Some (DMRR.f0 @rv))
      LCSA.AtomName "f1" -> pure (Some (DMRR.f1 @rv))
      LCSA.AtomName "f2" -> pure (Some (DMRR.f2 @rv))
      LCSA.AtomName "f3" -> pure (Some (DMRR.f3 @rv))
      LCSA.AtomName "f4" -> pure (Some (DMRR.f4 @rv))
      LCSA.AtomName "f5" -> pure (Some (DMRR.f5 @rv))
      LCSA.AtomName "f6" -> pure (Some (DMRR.f6 @rv))
      LCSA.AtomName "f7" -> pure (Some (DMRR.f7 @rv))
      LCSA.AtomName "f8" -> pure (Some (DMRR.f8 @rv))
      LCSA.AtomName "f9" -> pure (Some (DMRR.f9 @rv))
      LCSA.AtomName "f10" -> pure (Some (DMRR.f10 @rv))
      LCSA.AtomName "f11" -> pure (Some (DMRR.f11 @rv))
      LCSA.AtomName "f12" -> pure (Some (DMRR.f12 @rv))
      LCSA.AtomName "f13" -> pure (Some (DMRR.f13 @rv))
      LCSA.AtomName "f14" -> pure (Some (DMRR.f14 @rv))
      LCSA.AtomName "f15" -> pure (Some (DMRR.f15 @rv))
      LCSA.AtomName "f16" -> pure (Some (DMRR.f16 @rv))
      LCSA.AtomName "f17" -> pure (Some (DMRR.f17 @rv))
      LCSA.AtomName "f18" -> pure (Some (DMRR.f18 @rv))
      LCSA.AtomName "f19" -> pure (Some (DMRR.f19 @rv))
      LCSA.AtomName "f20" -> pure (Some (DMRR.f20 @rv))
      LCSA.AtomName "f21" -> pure (Some (DMRR.f21 @rv))
      LCSA.AtomName "f22" -> pure (Some (DMRR.f22 @rv))
      LCSA.AtomName "f23" -> pure (Some (DMRR.f23 @rv))
      LCSA.AtomName "f24" -> pure (Some (DMRR.f24 @rv))
      LCSA.AtomName "f25" -> pure (Some (DMRR.f25 @rv))
      LCSA.AtomName "f26" -> pure (Some (DMRR.f26 @rv))
      LCSA.AtomName "f27" -> pure (Some (DMRR.f27 @rv))
      LCSA.AtomName "f28" -> pure (Some (DMRR.f28 @rv))
      LCSA.AtomName "f29" -> pure (Some (DMRR.f29 @rv))
      LCSA.AtomName "f30" -> pure (Some (DMRR.f30 @rv))
      LCSA.AtomName "f31" -> pure (Some (DMRR.f31 @rv))
      LCSA.AtomName "mvendorid" -> pure (Some (DMRR.mvendorid @rv))
      LCSA.AtomName "marchid" -> pure (Some (DMRR.marchid @rv))
      LCSA.AtomName "mimpid" -> pure (Some (DMRR.mimpid @rv))
      LCSA.AtomName "mhartid" -> pure (Some (DMRR.mhartid @rv))
      LCSA.AtomName "mstatus" -> pure (Some (DMRR.mstatus @rv))
      LCSA.AtomName "misa" -> pure (Some (DMRR.misa @rv))
      LCSA.AtomName "medeleg" -> pure (Some (DMRR.medeleg @rv))
      LCSA.AtomName "mideleg" -> pure (Some (DMRR.mideleg @rv))
      LCSA.AtomName "mie" -> pure (Some (DMRR.mie @rv))
      LCSA.AtomName "mtvec" -> pure (Some (DMRR.mtvec @rv))
      LCSA.AtomName "mcounteren" -> pure (Some (DMRR.mcounteren @rv))
      LCSA.AtomName "mscratch" -> pure (Some (DMRR.mscratch @rv))
      LCSA.AtomName "mepc" -> pure (Some (DMRR.mepc @rv))
      LCSA.AtomName "mcause" -> pure (Some (DMRR.mcause @rv))
      LCSA.AtomName "mtval" -> pure (Some (DMRR.mtval @rv))
      LCSA.AtomName "mip" -> pure (Some (DMRR.mip @rv))
      LCSA.AtomName "mcycle" -> pure (Some (DMRR.mcycle @rv))
      LCSA.AtomName "minstret" -> pure (Some (DMRR.minstret @rv))
      LCSA.AtomName "mcycleh" -> pure (Some (DMRR.mcycleh @rv))
      LCSA.AtomName "minstreth" -> pure (Some (DMRR.minstreth @rv))
      LCSA.AtomName "frm" -> pure (Some (DMRR.frm @rv))
      LCSA.AtomName "fflags" -> pure (Some (DMRR.fflags @rv))
      LCSA.AtomName "fcsr" -> pure (Some (DMRR.fcsr @rv))
      LCSA.AtomName "priv" -> pure (Some (DMRR.priv @rv))
      LCSA.AtomName "exc" -> pure (Some (DMRR.exc @rv))
      LCSA.AtomName _ -> empty

riscvAtomParser ::
  forall rv m s ext.
  ( LCSM.MonadSyntax LCSA.Atomic m
  , MonadIO m
  , MonadState (LCSC.SyntaxState s) m
  , MonadWriter [Posd (Stmt ext s)] m
  , IsSyntaxExtension ext
  , ?parserHooks :: LCSC.ParserHooks ext
  , G.KnownRV rv
  , DMR.RISCVConstraints rv
  ) =>
  G.RVRepr rv ->
  m (Some (Atom s))
riscvAtomParser rv =
  LCSM.depCons LCSC.atomName $
    \case
      LCSA.AtomName "get-reg" -> do
        loc <- LCSM.position
        (Some reg, regs) <- LCSM.cons (parseReg rv) (parseRegs rv)
        let regTy = riscvRegTypes rv Ctx.! reg
        Some <$> LCSC.freshAtom loc (Reg.EvalApp (Expr.GetStruct regs reg regTy))
      LCSA.AtomName "set-reg" -> do
        loc <- LCSM.position
        LCSM.depCons (parseReg rv) $ \(Some reg) -> do
          let regTy = riscvRegTypes rv Ctx.! reg
          assign <- LCSC.operands (Ctx.Empty Ctx.:> regTy Ctx.:> riscvRegStructType rv)
          let (rest, regs) = Ctx.decompose assign
          let (Ctx.Empty, val) = Ctx.decompose rest
          Some <$> LCSC.freshAtom loc (Reg.EvalApp (Expr.SetStruct (riscvRegTypes rv) regs reg val))
      LCSA.AtomName _ -> empty
