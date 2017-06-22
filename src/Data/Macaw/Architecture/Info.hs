{-|
Copyright  : (c) Galois, Inc 2016
Maintainer : jhendrix@galois.com

This defines the architecture-specific information needed for code discovery.
-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
module Data.Macaw.Architecture.Info
  ( ArchitectureInfo(..)
  , DisassembleFn
  , archPostSyscallAbsState
  , Block(..)
  ) where

import Control.Monad.ST
import Data.Parameterized.Nonce
import Data.Word
import Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

import Data.Macaw.AbsDomain.AbsState as AbsState
import Data.Macaw.CFG
import Data.Macaw.Memory

------------------------------------------------------------------------
-- Block

-- | The type for code blocks returned by the disassembler.
--
-- The discovery process will attempt to map each block to a suitable ParsedBlock.

-- | A basic block in a control flow graph.
data Block arch ids
   = Block { blockLabel :: !Word64
             -- ^ Index of this block
           , blockStmts :: !([Stmt arch ids])
             -- ^ List of statements in the block.
           , blockTerm :: !(TermStmt arch ids)
             -- ^ The last statement in the block.
           }

instance ArchConstraints arch => Pretty (Block arch ids) where
  pretty b = do
    text (show (blockLabel b)) PP.<> text ":" <$$>
      indent 2 (vcat (pretty <$> blockStmts b) <$$> pretty (blockTerm b))



-- | Function for disassembling a block.
--
-- A block is defined as a contiguous region of code with a single known
-- entrance and potentially multiple exits.
--
-- This returns the list of blocks, the number of bytes in the blocks,
-- and any potential error that prematurely terminated translating the
-- block.
type DisassembleFn arch
   = forall ids
   .  NonceGenerator (ST ids) ids
   -> SegmentedAddr (ArchAddrWidth arch)
      -- ^ Segment that we are disassembling from
   -> MemWord (ArchAddrWidth arch)
      -- ^ Maximum offset for this to read from.
   -> AbsBlockState (ArchReg arch)
      -- ^ Abstract state associated with address that we are disassembling
      -- from.
      --
      -- This is used for things like the height of the x87 stack.
   -> ST ids ([Block arch ids], MemWord (ArchAddrWidth arch), Maybe String)

-- | This records architecture specific functions for analysis.
data ArchitectureInfo arch
   = ArchitectureInfo
     { withArchConstraints :: forall a . (ArchConstraints arch => a) -> a
       -- ^ Provides the architecture constraints to any computation
       -- that needs it.
     , archAddrWidth :: !(AddrWidthRepr (RegAddrWidth (ArchReg arch)))
       -- ^ Architecture address width.
     , archEndianness :: !Endianness
       -- ^ The byte order values are stored in.
     , jumpTableEntrySize :: !(MemWord (ArchAddrWidth arch))
       -- ^ The size of each entry in a jump table.
     , disassembleFn :: !(DisassembleFn arch)
       -- ^ Function for disasembling a block.
     , preserveRegAcrossSyscall :: !(forall tp . ArchReg arch tp -> Bool)
       -- ^ Return true if architecture register should be preserved across a system call.
     , mkInitialAbsState :: !(Memory (RegAddrWidth (ArchReg arch))
                         -> SegmentedAddr (RegAddrWidth (ArchReg arch))
                         -> AbsBlockState (ArchReg arch))
       -- ^ Creates an abstract block state for representing the beginning of a
       -- function.
     , absEvalArchFn :: !(forall ids tp
                          .  AbsProcessorState (ArchReg arch) ids
                          -> ArchFn arch ids tp
                          -> AbsValue (RegAddrWidth (ArchReg arch)) tp)
       -- ^ Evaluates an architecture-specific function
     , absEvalArchStmt :: !(forall ids
                            .  AbsProcessorState (ArchReg arch) ids
                            -> ArchStmt arch ids
                            -> AbsProcessorState (ArchReg arch) ids)
       -- ^ Evaluates an architecture-specific statement
     , postCallAbsState :: AbsBlockState (ArchReg arch)
                        -> SegmentedAddr (RegAddrWidth (ArchReg arch))
                        -> AbsBlockState (ArchReg arch)
       -- ^ Update the abstract state after a function call returns
     , identifyReturn :: forall ids
                      .  [Stmt arch ids]
                      -> RegState (ArchReg arch) (Value arch ids)
                      -> Maybe [Stmt arch ids]
       -- ^ Identify returns to the classifier.
       --
       -- Given a list of statements and the final state of the registers, this
       -- should return 'Just stmts' if this code looks like a function return.
       -- The stmts should be a subset of the statements, but may remove unneeded memory
       -- accesses like reading the stack pointer.
     }


-- | Return state post call
archPostSyscallAbsState :: ArchitectureInfo arch
                           -- ^ Architecture information
                        -> AbsBlockState (ArchReg arch)
                        -> SegmentedAddr (RegAddrWidth (ArchReg arch))
                        -> AbsBlockState (ArchReg arch)
archPostSyscallAbsState info = withArchConstraints info $ AbsState.absEvalCall params
  where params = CallParams { postCallStackDelta = 0
                            , preserveReg = preserveRegAcrossSyscall info
                            }
