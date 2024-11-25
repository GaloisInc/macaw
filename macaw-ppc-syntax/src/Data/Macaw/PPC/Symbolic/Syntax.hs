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

-- | 'LCSC.ParserHooks' for parsing macaw-ppc-symbolic CFGs.
module Data.Macaw.PPC.Symbolic.Syntax
  ( ppcParserHooks
  , ppc32ParserHooks
  , ppc64ParserHooks
    -- * Types
  , ppcTypeParser
    -- * Operations
  , parseRegs
  , parseReg
  , ppcAtomParser
  ) where

import Control.Applicative ( empty )
import Control.Monad qualified as Monad
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State.Strict (MonadState)
import Control.Monad.Writer.Strict (MonadWriter)
import Data.Text qualified as Text
import GHC.TypeNats ( type (<=) )

import Data.Macaw.Memory qualified as DMM
import Data.Macaw.Symbolic qualified as DMS
import Data.Macaw.PPC qualified as PPC
import Data.Macaw.PPC.Symbolic qualified as PPCS
import Data.Macaw.PPC.Symbolic.Regs qualified as PPCR
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(..))
import Lang.Crucible.CFG.Expr as Expr
import Lang.Crucible.CFG.Reg (Atom, Stmt)
import Lang.Crucible.CFG.Reg qualified as Reg
import Lang.Crucible.Syntax.Atoms qualified as LCSA
import Lang.Crucible.Syntax.Concrete qualified as LCSC
import Lang.Crucible.Syntax.Monad qualified as LCSM
import Lang.Crucible.Types qualified as LCT
import SemMC.Architecture.PPC qualified as SAP
import What4.ProgramLoc (Posd(..))

-- | Parser hooks for macaw-ppc-symbolic CFGs
ppcParserHooks ::
  forall v ext.
  ( PPC.KnownVariant v
  , 1 <= SAP.AddrWidth v
  , DMM.MemWidth (SAP.AddrWidth v)
  ) =>
  PPC.VariantRepr v ->
  LCSC.ParserHooks ext
ppcParserHooks v =
  LCSC.ParserHooks
  { LCSC.extensionTypeParser = ppcTypeParser v
  , LCSC.extensionParser = ppcAtomParser v
  }

-- | 'ppcParserHooks' instantiated to PPC32.
ppc32ParserHooks :: LCSC.ParserHooks ext
ppc32ParserHooks = ppcParserHooks PPC.V32Repr

-- | 'ppcParserHooks' instantiated to PPC64.
ppc64ParserHooks :: LCSC.ParserHooks ext
ppc64ParserHooks = ppcParserHooks PPC.V64Repr

---------------------------------------------------------------------
-- Types

-- Helper, not exported
namedAtom :: LCSM.MonadSyntax LCSA.Atomic m => Text.Text -> m ()
namedAtom expectName = do
  name <- LCSC.atomName
  Monad.unless (name == LCSA.AtomName expectName) LCSM.cut

-- Helper, not exported
ppcRegTypes ::
  ( PPC.KnownVariant v
  , 1 <= SAP.AddrWidth v
  , DMM.MemWidth (SAP.AddrWidth v)
  ) =>
  Ctx.Assignment LCT.TypeRepr (DMS.MacawCrucibleRegTypes (PPC.AnyPPC v))
ppcRegTypes = DMS.crucArchRegTypes PPCS.ppcMacawSymbolicFns

-- Helper, not exported
ppcRegStructType ::
  ( PPC.KnownVariant v
  , 1 <= SAP.AddrWidth v
  , DMM.MemWidth (SAP.AddrWidth v)
  ) =>
  LCT.TypeRepr (DMS.ArchRegStruct (PPC.AnyPPC v))
ppcRegStructType = LCT.StructRepr ppcRegTypes

-- Helper, not exported
ppcRegsName :: PPC.VariantRepr v -> Text.Text
ppcRegsName PPC.V32Repr = "PPC32Regs"
ppcRegsName PPC.V64Repr = "PPC64Regs"

-- | Parser for type extensions to Crucible syntax
ppcTypeParser ::
  forall v m.
  ( LCSM.MonadSyntax LCSA.Atomic m
  , PPC.KnownVariant v
  , 1 <= SAP.AddrWidth v
  , DMM.MemWidth (SAP.AddrWidth v)
  ) =>
  PPC.VariantRepr v ->
  m (Some LCT.TypeRepr)
ppcTypeParser v = do
  namedAtom (ppcRegsName v)
  pure (Some (ppcRegStructType @v))

---------------------------------------------------------------------
-- Operations

parseRegs ::
  ( LCSM.MonadSyntax LCSA.Atomic m
  , MonadIO m
  , MonadState (LCSC.SyntaxState s) m
  , MonadWriter [Posd (Stmt ext s)] m
  , IsSyntaxExtension ext
  , ?parserHooks :: LCSC.ParserHooks ext
  , PPC.KnownVariant v
  , 1 <= SAP.AddrWidth v
  , DMM.MemWidth (SAP.AddrWidth v)
  ) =>
  m (Atom s (DMS.ArchRegStruct (PPC.AnyPPC v)))
parseRegs =
  LCSM.describe "a struct of PowerPC register values" $ do
    assign <- LCSC.operands (Ctx.Empty Ctx.:> ppcRegStructType)
    pure (assign Ctx.! Ctx.baseIndex)

parseReg :: LCSM.MonadSyntax LCSA.Atomic m => m (Some (Ctx.Index (DMS.MacawCrucibleRegTypes (PPC.AnyPPC v))))
parseReg =
  LCSM.describe "a PowerPC register" $ do
    name <- LCSC.atomName
    case name of
      LCSA.AtomName "ip" -> pure (Some PPCR.ip)
      LCSA.AtomName "lnk" -> pure (Some PPCR.lnk)
      LCSA.AtomName "ctr" -> pure (Some PPCR.ctr)
      LCSA.AtomName "xer" -> pure (Some PPCR.xer)
      LCSA.AtomName "cr" -> pure (Some PPCR.cr)
      LCSA.AtomName "fpscr" -> pure (Some PPCR.fpscr)
      LCSA.AtomName "vscr" -> pure (Some PPCR.vscr)
      LCSA.AtomName "r0" -> pure (Some PPCR.r0)
      LCSA.AtomName "r1" -> pure (Some PPCR.r1)
      LCSA.AtomName "r2" -> pure (Some PPCR.r2)
      LCSA.AtomName "r3" -> pure (Some PPCR.r3)
      LCSA.AtomName "r4" -> pure (Some PPCR.r4)
      LCSA.AtomName "r5" -> pure (Some PPCR.r5)
      LCSA.AtomName "r6" -> pure (Some PPCR.r6)
      LCSA.AtomName "r7" -> pure (Some PPCR.r7)
      LCSA.AtomName "r8" -> pure (Some PPCR.r8)
      LCSA.AtomName "r9" -> pure (Some PPCR.r9)
      LCSA.AtomName "r10" -> pure (Some PPCR.r10)
      LCSA.AtomName "r11" -> pure (Some PPCR.r11)
      LCSA.AtomName "r12" -> pure (Some PPCR.r12)
      LCSA.AtomName "r13" -> pure (Some PPCR.r13)
      LCSA.AtomName "r14" -> pure (Some PPCR.r14)
      LCSA.AtomName "r15" -> pure (Some PPCR.r15)
      LCSA.AtomName "r16" -> pure (Some PPCR.r16)
      LCSA.AtomName "r17" -> pure (Some PPCR.r17)
      LCSA.AtomName "r18" -> pure (Some PPCR.r18)
      LCSA.AtomName "r19" -> pure (Some PPCR.r19)
      LCSA.AtomName "r20" -> pure (Some PPCR.r20)
      LCSA.AtomName "r21" -> pure (Some PPCR.r21)
      LCSA.AtomName "r22" -> pure (Some PPCR.r22)
      LCSA.AtomName "r23" -> pure (Some PPCR.r23)
      LCSA.AtomName "r24" -> pure (Some PPCR.r24)
      LCSA.AtomName "r25" -> pure (Some PPCR.r25)
      LCSA.AtomName "r26" -> pure (Some PPCR.r26)
      LCSA.AtomName "r27" -> pure (Some PPCR.r27)
      LCSA.AtomName "r28" -> pure (Some PPCR.r28)
      LCSA.AtomName "r29" -> pure (Some PPCR.r29)
      LCSA.AtomName "r30" -> pure (Some PPCR.r30)
      LCSA.AtomName "r31" -> pure (Some PPCR.r31)
      LCSA.AtomName "f0" -> pure (Some PPCR.f0)
      LCSA.AtomName "f1" -> pure (Some PPCR.f1)
      LCSA.AtomName "f2" -> pure (Some PPCR.f2)
      LCSA.AtomName "f3" -> pure (Some PPCR.f3)
      LCSA.AtomName "f4" -> pure (Some PPCR.f4)
      LCSA.AtomName "f5" -> pure (Some PPCR.f5)
      LCSA.AtomName "f6" -> pure (Some PPCR.f6)
      LCSA.AtomName "f7" -> pure (Some PPCR.f7)
      LCSA.AtomName "f8" -> pure (Some PPCR.f8)
      LCSA.AtomName "f9" -> pure (Some PPCR.f9)
      LCSA.AtomName "f10" -> pure (Some PPCR.f10)
      LCSA.AtomName "f11" -> pure (Some PPCR.f11)
      LCSA.AtomName "f12" -> pure (Some PPCR.f12)
      LCSA.AtomName "f13" -> pure (Some PPCR.f13)
      LCSA.AtomName "f14" -> pure (Some PPCR.f14)
      LCSA.AtomName "f15" -> pure (Some PPCR.f15)
      LCSA.AtomName "f16" -> pure (Some PPCR.f16)
      LCSA.AtomName "f17" -> pure (Some PPCR.f17)
      LCSA.AtomName "f18" -> pure (Some PPCR.f18)
      LCSA.AtomName "f19" -> pure (Some PPCR.f19)
      LCSA.AtomName "f20" -> pure (Some PPCR.f20)
      LCSA.AtomName "f21" -> pure (Some PPCR.f21)
      LCSA.AtomName "f22" -> pure (Some PPCR.f22)
      LCSA.AtomName "f23" -> pure (Some PPCR.f23)
      LCSA.AtomName "f24" -> pure (Some PPCR.f24)
      LCSA.AtomName "f25" -> pure (Some PPCR.f25)
      LCSA.AtomName "f26" -> pure (Some PPCR.f26)
      LCSA.AtomName "f27" -> pure (Some PPCR.f27)
      LCSA.AtomName "f28" -> pure (Some PPCR.f28)
      LCSA.AtomName "f29" -> pure (Some PPCR.f29)
      LCSA.AtomName "f30" -> pure (Some PPCR.f30)
      LCSA.AtomName "f31" -> pure (Some PPCR.f31)
      LCSA.AtomName _ -> empty

ppcAtomParser ::
  forall v m s ext.
  ( LCSM.MonadSyntax LCSA.Atomic m
  , MonadIO m
  , MonadState (LCSC.SyntaxState s) m
  , MonadWriter [Posd (Stmt ext s)] m
  , IsSyntaxExtension ext
  , ?parserHooks :: LCSC.ParserHooks ext
  , PPC.KnownVariant v
  , 1 <= SAP.AddrWidth v
  , DMM.MemWidth (SAP.AddrWidth v)
  ) =>
  PPC.VariantRepr v ->
  m (Some (Atom s))
ppcAtomParser _ =
  LCSM.depCons LCSC.atomName $
    \case
      LCSA.AtomName "get-reg" -> do
        loc <- LCSM.position
        (Some reg, regs) <- LCSM.cons parseReg parseRegs
        let regTy = ppcRegTypes @v Ctx.! reg
        Some <$> LCSC.freshAtom loc (Reg.EvalApp (Expr.GetStruct regs reg regTy))
      LCSA.AtomName "set-reg" -> do
        loc <- LCSM.position
        LCSM.depCons parseReg $ \(Some reg) -> do
          let regTy = ppcRegTypes @v Ctx.! reg
          assign <- LCSC.operands (Ctx.Empty Ctx.:> regTy Ctx.:> ppcRegStructType)
          let (rest, regs) = Ctx.decompose assign
          let (Ctx.Empty, val) = Ctx.decompose rest
          Some <$> LCSC.freshAtom loc (Reg.EvalApp (Expr.SetStruct ppcRegTypes regs reg val))
      LCSA.AtomName _ -> empty
