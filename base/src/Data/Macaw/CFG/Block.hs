{-|
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This exports the pre-classification term statement and block data
types.
-}
{-# LANGUAGE FlexibleContexts #-}
module Data.Macaw.CFG.Block
  ( Block(..)
  , ppBlock
  , TermStmt(..)
  ) where

import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import           Data.Macaw.CFG.Core
import           Data.Macaw.Types

------------------------------------------------------------------------
-- TermStmt

-- | A terminal statement in a block
--
-- This is the unclassified definition that is generated directly from
-- the architecture specific disassembler.
data TermStmt arch ids
     -- | Fetch and execute the next instruction from the given processor state.
  = FetchAndExecute !(RegState (ArchReg arch) (Value arch ids))
    -- | Branch and execute one block or another.
  | Branch !(Value arch ids BoolType) !Word64 !Word64
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
    -- The address returns the address within the current function that this terminal
    -- statement could return to (if any)
  | ArchTermStmt !(ArchTermStmt arch ids)
                 !(RegState (ArchReg arch) (Value arch ids))

instance ArchConstraints arch
      => Pretty (TermStmt arch ids) where
  pretty (FetchAndExecute s) =
    text "fetch_and_execute" <$$>
    indent 2 (pretty s)
  pretty (Branch c x y) =
    text "branch" <+> ppValue 0 c <+> text (show x) <+> text (show y)
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
data Block arch ids
   = Block { blockLabel :: !Word64
             -- ^ Index of this block
           , blockStmts :: !([Stmt arch ids])
             -- ^ List of statements in the block.
           , blockTerm :: !(TermStmt arch ids)
             -- ^ The last statement in the block.
           }

ppBlock :: ArchConstraints arch => Block arch ids -> Doc
ppBlock b =
  text (show (blockLabel b)) PP.<> text ":" <$$>
  indent 2 (vcat (ppStmt (text . show) <$> blockStmts b) <$$> pretty (blockTerm b))
