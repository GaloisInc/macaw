{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | 'LCSC.ParserHooks' for parsing macaw-x86-symbolic CFGs.
module Data.Macaw.X86.Symbolic.Syntax
  ( x86ParserHooks
    -- * Types
  , x86TypeParser
    -- * Operations
  , parseRegs
  , parseReg
  , x86AtomParser
  ) where

import Control.Applicative ( empty )
import Control.Monad qualified as Monad
import Control.Monad.IO.Class (MonadIO)
import Control.Monad.State.Strict (MonadState)
import Control.Monad.Writer.Strict (MonadWriter)
import Data.Text qualified as Text

import Data.Macaw.Symbolic qualified as DMS
import Data.Macaw.X86 qualified as X86
import Data.Macaw.X86.Symbolic qualified as X86
import Data.Parameterized.Context qualified as Ctx
import Data.Parameterized.Some (Some(..))
import Lang.Crucible.CFG.Expr as Expr
import Lang.Crucible.CFG.Reg (Atom, Stmt)
import Lang.Crucible.CFG.Reg qualified as Reg
import Lang.Crucible.LLVM.MemModel.Pointer qualified as Mem
import Lang.Crucible.Syntax.Atoms qualified as LCSA
import Lang.Crucible.Syntax.Concrete qualified as LCSC
import Lang.Crucible.Syntax.Monad qualified as LCSM
import Lang.Crucible.Types qualified as LCT
import What4.ProgramLoc (Posd(..))

-- | Parser hooks for macaw-x86-symbolic CFGs
x86ParserHooks :: LCSC.ParserHooks ext
x86ParserHooks =
  LCSC.ParserHooks
  { LCSC.extensionTypeParser = x86TypeParser
  , LCSC.extensionParser = x86AtomParser
  }

---------------------------------------------------------------------
-- Types

-- Helper, not exported
namedAtom :: LCSM.MonadSyntax LCSA.Atomic m => Text.Text -> m ()
namedAtom expectName = do
  name <- LCSC.atomName
  Monad.unless (name == LCSA.AtomName expectName) LCSM.cut

-- Helper, not exported
x86RegTypes :: Ctx.Assignment LCT.TypeRepr (DMS.MacawCrucibleRegTypes X86.X86_64)
x86RegTypes = DMS.crucArchRegTypes X86.x86_64MacawSymbolicFns

-- Helper, not exported
x86RegStructType :: LCT.TypeRepr (DMS.ArchRegStruct X86.X86_64)
x86RegStructType = LCT.StructRepr x86RegTypes

-- | Parser for type extensions to Crucible syntax
x86TypeParser ::
  LCSM.MonadSyntax LCSA.Atomic m =>
  m (Some LCT.TypeRepr)
x86TypeParser = do
  namedAtom "X86Regs"
  pure (Some x86RegStructType)

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
  m (Atom s (DMS.ArchRegStruct X86.X86_64))
parseRegs =
  LCSM.describe "a struct of x86_64 register values" $ do
    assign <- LCSC.operands (Ctx.Empty Ctx.:> x86RegStructType)
    pure (assign Ctx.! Ctx.baseIndex)

parseReg :: LCSM.MonadSyntax LCSA.Atomic m => m (Some (Ctx.Index (DMS.MacawCrucibleRegTypes X86.X86_64)))
parseReg =
  LCSM.describe "an x86_64 register" $ do
    name <- LCSC.atomName
    case name of
      LCSA.AtomName "rip" ->
        pure (Some ripIndex)
      LCSA.AtomName _ -> empty

ripIndex :: Ctx.Index (DMS.MacawCrucibleRegTypes X86.X86_64) (Mem.LLVMPointerType 64)
ripIndex = Ctx.extendIndex @(Ctx.EmptyCtx Ctx.::> Mem.LLVMPointerType 64) @(DMS.MacawCrucibleRegTypes X86.X86_64) Ctx.baseIndex

x86AtomParser ::
  ( LCSM.MonadSyntax LCSA.Atomic m
  , MonadIO m
  , MonadState (LCSC.SyntaxState s) m
  , MonadWriter [Posd (Stmt ext s)] m
  , IsSyntaxExtension ext
  , ?parserHooks :: LCSC.ParserHooks ext
  ) =>
  m (Some (Atom s))
x86AtomParser =
  LCSM.depCons LCSC.atomName $
    \case
      LCSA.AtomName "get-reg" -> do
        loc <- LCSM.position
        (Some reg, regs) <- LCSM.cons parseReg parseRegs
        let regTy = x86RegTypes Ctx.! reg
        Some <$> LCSC.freshAtom loc (Reg.EvalApp (Expr.GetStruct regs reg regTy))
      LCSA.AtomName _ -> empty
