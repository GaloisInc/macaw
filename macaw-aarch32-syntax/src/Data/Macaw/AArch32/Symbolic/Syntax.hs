{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

-- | 'LCSC.ParserHooks' for parsing macaw-aarch32-symbolic CFGs.
module Data.Macaw.AArch32.Symbolic.Syntax
  ( aarch32ParserHooks
    -- * Types
  , aarch32TypeParser
    -- * Operations
  , parseRegs
  , parseReg
  , aarch32AtomParser
  ) where

import Control.Applicative ( empty )
import Control.Monad qualified as Monad
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State.Strict (MonadState)
import Control.Monad.Writer.Strict (MonadWriter)
import Data.Text qualified as Text

import Data.Macaw.Symbolic qualified as DMS
import Data.Macaw.ARM qualified as ARM
import Data.Macaw.AArch32.Symbolic qualified as AArch32
import Data.Macaw.AArch32.Symbolic.Regs qualified as AArch32R
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(..))
import Lang.Crucible.CFG.Expr as Expr
import Lang.Crucible.CFG.Reg (Atom, Stmt)
import Lang.Crucible.CFG.Reg qualified as Reg
import Lang.Crucible.Syntax.Atoms qualified as LCSA
import Lang.Crucible.Syntax.Concrete qualified as LCSC
import Lang.Crucible.Syntax.Monad qualified as LCSM
import Lang.Crucible.Types qualified as LCT
import What4.ProgramLoc (Posd(..))

-- | Parser hooks for macaw-aarch32-symbolic CFGs
aarch32ParserHooks :: LCSC.ParserHooks ext
aarch32ParserHooks =
  LCSC.ParserHooks
  { LCSC.extensionTypeParser = aarch32TypeParser
  , LCSC.extensionParser = aarch32AtomParser
  }

---------------------------------------------------------------------
-- Types

-- Helper, not exported
namedAtom :: LCSM.MonadSyntax LCSA.Atomic m => Text.Text -> m ()
namedAtom expectName = do
  name <- LCSC.atomName
  Monad.unless (name == LCSA.AtomName expectName) LCSM.cut

-- Helper, not exported
aarch32RegTypes :: Ctx.Assignment LCT.TypeRepr (DMS.MacawCrucibleRegTypes ARM.ARM)
aarch32RegTypes = DMS.crucArchRegTypes AArch32.aarch32MacawSymbolicFns

-- Helper, not exported
aarch32RegStructType :: LCT.TypeRepr (DMS.ArchRegStruct ARM.ARM)
aarch32RegStructType = LCT.StructRepr aarch32RegTypes

-- | Parser for type extensions to Crucible syntax
aarch32TypeParser ::
  LCSM.MonadSyntax LCSA.Atomic m =>
  m (Some LCT.TypeRepr)
aarch32TypeParser = do
  namedAtom "AArch32Regs"
  pure (Some aarch32RegStructType)

---------------------------------------------------------------------
-- Operations

parseRegs ::
  ( LCSM.MonadSyntax LCSA.Atomic m
  , MonadIO m
  , MonadState (LCSC.SyntaxState s) m
  , MonadWriter [Posd (Stmt ext s)] m
  , IsSyntaxExtension ext
  , ?parserHooks :: LCSC.ParserHooks ext
  ) =>
  m (Atom s (DMS.ArchRegStruct ARM.ARM))
parseRegs =
  LCSM.describe "a struct of AArch32 register values" $ do
    assign <- LCSC.operands (Ctx.Empty Ctx.:> aarch32RegStructType)
    pure (assign Ctx.! Ctx.baseIndex)

parseReg :: LCSM.MonadSyntax LCSA.Atomic m => m (Some (Ctx.Index (DMS.MacawCrucibleRegTypes ARM.ARM)))
parseReg =
  LCSM.describe "an AArch32 register" $ do
    name <- LCSC.atomName
    case name of
      LCSA.AtomName "r0" -> pure (Some AArch32R.r0)
      LCSA.AtomName "r1" -> pure (Some AArch32R.r1)
      LCSA.AtomName "r2" -> pure (Some AArch32R.r2)
      LCSA.AtomName "r3" -> pure (Some AArch32R.r3)
      LCSA.AtomName "r4" -> pure (Some AArch32R.r4)
      LCSA.AtomName "r5" -> pure (Some AArch32R.r5)
      LCSA.AtomName "r6" -> pure (Some AArch32R.r6)
      LCSA.AtomName "r7" -> pure (Some AArch32R.r7)
      LCSA.AtomName "r8" -> pure (Some AArch32R.r8)
      LCSA.AtomName "r9" -> pure (Some AArch32R.r9)
      LCSA.AtomName "r10" -> pure (Some AArch32R.r10)
      LCSA.AtomName "r11" -> pure (Some AArch32R.r11)
      LCSA.AtomName "fp" -> pure (Some AArch32R.fp)
      LCSA.AtomName "r12" -> pure (Some AArch32R.r12)
      LCSA.AtomName "ip" -> pure (Some AArch32R.ip)
      LCSA.AtomName "r13" -> pure (Some AArch32R.r13)
      LCSA.AtomName "sp" -> pure (Some AArch32R.sp)
      LCSA.AtomName "r14" -> pure (Some AArch32R.r14)
      LCSA.AtomName "lr" -> pure (Some AArch32R.lr)
      LCSA.AtomName "v0" -> pure (Some AArch32R.v0)
      LCSA.AtomName "v1" -> pure (Some AArch32R.v1)
      LCSA.AtomName "v2" -> pure (Some AArch32R.v2)
      LCSA.AtomName "v3" -> pure (Some AArch32R.v3)
      LCSA.AtomName "v4" -> pure (Some AArch32R.v4)
      LCSA.AtomName "v5" -> pure (Some AArch32R.v5)
      LCSA.AtomName "v6" -> pure (Some AArch32R.v6)
      LCSA.AtomName "v7" -> pure (Some AArch32R.v7)
      LCSA.AtomName "v8" -> pure (Some AArch32R.v8)
      LCSA.AtomName "v9" -> pure (Some AArch32R.v9)
      LCSA.AtomName "v10" -> pure (Some AArch32R.v10)
      LCSA.AtomName "v11" -> pure (Some AArch32R.v11)
      LCSA.AtomName "v12" -> pure (Some AArch32R.v12)
      LCSA.AtomName "v13" -> pure (Some AArch32R.v13)
      LCSA.AtomName "v14" -> pure (Some AArch32R.v14)
      LCSA.AtomName "v15" -> pure (Some AArch32R.v15)
      LCSA.AtomName "v16" -> pure (Some AArch32R.v16)
      LCSA.AtomName "v17" -> pure (Some AArch32R.v17)
      LCSA.AtomName "v18" -> pure (Some AArch32R.v18)
      LCSA.AtomName "v19" -> pure (Some AArch32R.v19)
      LCSA.AtomName "v20" -> pure (Some AArch32R.v20)
      LCSA.AtomName "v21" -> pure (Some AArch32R.v21)
      LCSA.AtomName "v22" -> pure (Some AArch32R.v22)
      LCSA.AtomName "v23" -> pure (Some AArch32R.v23)
      LCSA.AtomName "v24" -> pure (Some AArch32R.v24)
      LCSA.AtomName "v25" -> pure (Some AArch32R.v25)
      LCSA.AtomName "v26" -> pure (Some AArch32R.v26)
      LCSA.AtomName "v27" -> pure (Some AArch32R.v27)
      LCSA.AtomName "v28" -> pure (Some AArch32R.v28)
      LCSA.AtomName "v29" -> pure (Some AArch32R.v29)
      LCSA.AtomName "v30" -> pure (Some AArch32R.v30)
      LCSA.AtomName "v31" -> pure (Some AArch32R.v31)
      LCSA.AtomName _ -> empty

aarch32AtomParser ::
  ( LCSM.MonadSyntax LCSA.Atomic m
  , MonadIO m
  , MonadState (LCSC.SyntaxState s) m
  , MonadWriter [Posd (Stmt ext s)] m
  , IsSyntaxExtension ext
  , ?parserHooks :: LCSC.ParserHooks ext
  ) =>
  m (Some (Atom s))
aarch32AtomParser =
  LCSM.depCons LCSC.atomName $
    \case
      LCSA.AtomName "get-reg" -> do
        loc <- LCSM.position
        (Some reg, regs) <- LCSM.cons parseReg parseRegs
        let regTy = aarch32RegTypes Ctx.! reg
        Some <$> LCSC.freshAtom loc (Reg.EvalApp (Expr.GetStruct regs reg regTy))
      LCSA.AtomName "set-reg" -> do
        loc <- LCSM.position
        LCSM.depCons parseReg $ \(Some reg) -> do
          let regTy = aarch32RegTypes Ctx.! reg
          assign <- LCSC.operands (Ctx.Empty Ctx.:> regTy Ctx.:> aarch32RegStructType)
          let (rest, regs) = Ctx.decompose assign
          let (Ctx.Empty, val) = Ctx.decompose rest
          Some <$> LCSC.freshAtom loc (Reg.EvalApp (Expr.SetStruct aarch32RegTypes regs reg val))
      LCSA.AtomName _ -> empty
