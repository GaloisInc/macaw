{-|
Copyright        : (c) Galois, Inc 2017-2019
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This exports the pre-classification term statement and block data
types.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE PolyKinds #-}

module Data.Macaw.CFG.Block
  ( Block(..)
  , ppBlock
  , TermStmt(..)
  ) where

import           Data.Text (Text)
import qualified Data.Text as Text
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.CFG.Core

------------------------------------------------------------------------
-- TermStmt

-- | A terminal statement in a block
--
-- This is the unclassified definition that is generated directly from
-- the architecture specific disassembler.
data TermStmt (arch :: k) ids
     -- | Fetch and execute the next instruction from the given processor state.
  = FetchAndExecute !(RegState (ArchReg arch) (Value arch ids))
    -- | The block ended prematurely due to an error in instruction
    -- decoding or translation.
    --
    -- This contains the state of the registers when the translation error
    -- occured and the error message recorded.
  | TranslateError !(RegState (ArchReg arch) (Value arch ids)) !Text
    -- | An architecture specific term stmt.
    --
    -- The registers include the state of registers just before the terminal statement
    -- executes.
  | ArchTermStmt !(ArchTermStmt arch ids)
                 !(RegState (ArchReg arch) (Value arch ids))

instance ArchConstraints arch
      => Pretty (TermStmt arch ids) where
  pretty (FetchAndExecute s) =
    text "fetch_and_execute" <$$>
    indent 2 (pretty s)
  pretty (TranslateError s msg) =
    text "ERROR: " <+> text (Text.unpack msg) <$$>
    indent 2 (pretty s)
  pretty (ArchTermStmt ts regs) =
    prettyF ts <$$> indent 2 (pretty regs)

------------------------------------------------------------------------
-- Block

-- | The type for code blocks returned by the disassembler.
--
-- The discovery process will attempt to map each block to a suitable ParsedBlock.
data Block (arch :: k) ids
   = Block { blockStmts :: !([Stmt arch ids])
             -- ^ List of statements in the block.
           , blockTerm :: !(TermStmt arch ids)
             -- ^ The last statement in the block.
           }

ppBlock :: ArchConstraints arch => Block arch ids -> Doc
ppBlock b = vcat (ppStmt (text . show) <$> blockStmts b) <$$> pretty (blockTerm b)
