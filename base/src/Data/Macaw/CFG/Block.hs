{-|
Copyright        : (c) Galois, Inc 2017-2019
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This exports the pre-classification term statement and block data
types.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.CFG.Block
  ( Block(..)
  , ppBlock
  , TermStmt(..)
  ) where

import           Data.Text (Text)
import           Prettyprinter

import           Data.Macaw.CFG.Core

------------------------------------------------------------------------
-- TermStmt

-- | A terminal statement in a block
--
-- This is the unclassified definition that is generated directly from
-- the architecture specific disassembler.
data TermStmt arch ids
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
  | ArchTermStmt !(ArchTermStmt arch (Value arch ids))
                 !(RegState (ArchReg arch) (Value arch ids))

instance ArchConstraints arch
      => Pretty (TermStmt arch ids) where
  pretty (FetchAndExecute s) =
    vcat
    [ "fetch_and_execute"
    , indent 2 (pretty s) ]
  pretty (TranslateError s msg) =
    vcat
    [ "ERROR: " <+> pretty msg
    , indent 2 (pretty s) ]
  pretty (ArchTermStmt ts regs) =
    vcat
    [ ppArchTermStmt pretty ts
    , indent 2 (pretty regs) ]

------------------------------------------------------------------------
-- Block

-- | The type for code blocks returned by the disassembler.
--
-- The discovery process will attempt to map each block to a suitable ParsedBlock.
data Block arch ids
   = Block { blockStmts :: !([Stmt arch ids])
             -- ^ List of statements in the block.
           , blockTerm :: !(TermStmt arch ids)
             -- ^ The last statement in the block.
           }

ppBlock :: ArchConstraints arch => Block arch ids -> Doc ann
ppBlock b = vcat [vcat (ppStmt viaShow <$> blockStmts b), pretty (blockTerm b)]
