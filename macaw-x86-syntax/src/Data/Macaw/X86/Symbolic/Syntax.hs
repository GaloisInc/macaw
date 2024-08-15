{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}

-- | 'LCSC.ParserHooks' for parsing macaw-x86-symbolic CFGs.
module Data.Macaw.X86.Symbolic.Syntax
  ( x86ParserHooks
  , x86TypeParser
  ) where

import Control.Applicative ( empty )
import Control.Monad qualified as Monad
import Data.Text qualified as Text
import Data.Parameterized.Some ( Some(..) )

import Data.Macaw.Symbolic qualified as DMS
import Data.Macaw.X86 qualified as X86
import Data.Macaw.X86.Symbolic qualified as X86
import Lang.Crucible.Syntax.Atoms qualified as LCSA
import Lang.Crucible.Syntax.Concrete qualified as LCSC
import Lang.Crucible.Syntax.Monad qualified as LCSM
import Lang.Crucible.Types qualified as LCT

-- | Parser hooks for macaw-x86-symbolic CFGs
x86ParserHooks :: LCSC.ParserHooks ext
x86ParserHooks =
  LCSC.ParserHooks
  { LCSC.extensionTypeParser = x86TypeParser
  , LCSC.extensionParser = empty
  }

---------------------------------------------------------------------
-- Types

-- Helper, not exported
namedAtom :: LCSM.MonadSyntax LCSA.Atomic m => Text.Text -> m ()
namedAtom expectName = do
  name <- LCSC.atomName
  Monad.unless (name == LCSA.AtomName expectName) LCSM.cut

-- Helper, not exported
x86RegStructType :: LCT.TypeRepr (DMS.ArchRegStruct X86.X86_64)
x86RegStructType =
  LCT.StructRepr (DMS.crucArchRegTypes X86.x86_64MacawSymbolicFns)

-- | Parser for type extensions to Crucible syntax
x86TypeParser ::
  LCSM.MonadSyntax LCSA.Atomic m =>
  m (Some LCT.TypeRepr)
x86TypeParser = do
  namedAtom "X86Regs"
  pure (Some x86RegStructType)
