{-|
Copyright  : (c) Galois, Inc 2016
Maintainer : jhendrix@galois.com

This defines the architecture-specific information needed for code discovery.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
module Data.Macaw.Architecture.Info
  ( ArchitectureInfo(..)
  , DisassembleFn
    -- * Unclassified blocks
  , module Data.Macaw.CFG.Block
  , rewriteBlock
  ) where

import           Control.Monad.ST
import           Data.Parameterized.Nonce
import           Data.Parameterized.TraversableF
import           Data.Sequence (Seq)

import           Data.Macaw.AbsDomain.AbsState as AbsState
import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Block
import           Data.Macaw.CFG.Core
import           Data.Macaw.CFG.DemandSet
import           Data.Macaw.CFG.Rewriter
import           Data.Macaw.Memory

------------------------------------------------------------------------
-- ArchitectureInfo

-- | Function for disassembling a range of code (usually a function in
-- the target code image) into blocks.
--
-- A block is defined as a contiguous region of code with a single known
-- entrance and potentially multiple exits.
--
-- This returns the list of blocks, the number of bytes in the blocks,
-- and any potential error that prematurely terminated translating the
-- block.
type DisassembleFn arch
   = forall s ids
   .  NonceGenerator (ST s) ids
   -> ArchSegmentOff arch
      -- ^ The offset to start reading from.
   -> RegState (ArchReg arch) (Value arch ids)
      -- ^ Initial values to use for registers.
   -> Int
      -- ^ Maximum offset for this to read from.
   -> ST s ([Block arch ids], Int, Maybe String)

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
     , mkInitialRegsForBlock :: !(forall ids
                              .  ArchSegmentOff arch
                              -> AbsBlockState (ArchReg arch)
                              -> Either String (RegState (ArchReg arch) (Value arch ids)))
       -- ^ Use the abstract block state information to infer register
       -- values to use for disassembling from given address.
     , disassembleFn :: !(DisassembleFn arch)
       -- ^ Function for disassembling a block.
     , mkInitialAbsState :: !(Memory (RegAddrWidth (ArchReg arch))
                         -> ArchSegmentOff arch
                         -> AbsBlockState (ArchReg arch))
       -- ^ Creates an abstract block state for representing the beginning of a
       -- function.
       --
       -- The address is the entry point of the function.
     , absEvalArchFn :: !(forall ids tp
                          .  AbsProcessorState (ArchReg arch) ids
                          -> ArchFn arch (Value arch ids) tp
                          -> AbsValue (RegAddrWidth (ArchReg arch)) tp)
       -- ^ Evaluates an architecture-specific function
     , absEvalArchStmt :: !(forall ids
                            .  AbsProcessorState (ArchReg arch) ids
                            -> ArchStmt arch (Value arch ids)
                            -> AbsProcessorState (ArchReg arch) ids)
       -- ^ Evaluates an architecture-specific statement
     , postCallAbsState :: AbsBlockState (ArchReg arch)
                        -> ArchSegmentOff arch
                        -> AbsBlockState (ArchReg arch)
       -- ^ Update the abstract state after a function call returns
     , identifyCall :: forall ids
                    .  Memory (ArchAddrWidth arch)
                    -> Seq (Stmt arch ids)
                    -> RegState (ArchReg arch) (Value arch ids)
                    -> Maybe (Seq (Stmt arch ids), ArchSegmentOff arch)
       -- ^ Function for recognizing call statements.
       --
       -- Given a memory state, list of statements, and final register
       -- state, the should determine if this is a call, and if so,
       -- return the statements with any action to push the return
       -- value to the stack removed, and provide the return address that
       -- the function should return to.

     , checkForReturnAddr :: forall ids
                          .  RegState (ArchReg arch) (Value arch ids)
                          -> AbsProcessorState (ArchReg arch) ids
                          -> Bool
       -- ^ @checkForReturnAddr regs s@ returns true if the location
       -- where the return address is normally stored in regs when
       -- calling a function does indeed contain the abstract value
       -- associated with return addresses.
       --
       -- For x86 this checks if the address just above the stack is the
       -- return address.  For ARM, this should check the link register.
       --
       -- This predicate is invoked when considering if a potential tail call
       -- is setup to return to the right location.
     , identifyReturn :: forall ids
                      .  Seq (Stmt arch ids)
                      -> RegState (ArchReg arch) (Value arch ids)
                      -> AbsProcessorState (ArchReg arch) ids
                      -> Maybe (Seq (Stmt arch ids))
       -- ^ Identify returns to the classifier.
       --
       -- Given a list of statements and the final state of the registers, this
       -- should return 'Just stmts' if this code looks like a function return.
       -- The stmts should be a subset of the statements, but may remove unneeded memory
       -- accesses like reading the stack pointer.
     , rewriteArchFn :: (forall s src tgt tp
                         .  ArchFn arch (Value arch src) tp
                         -> Rewriter arch s src tgt (Value arch tgt tp))
       -- ^ This rewrites an architecture specific statement
     , rewriteArchStmt :: (forall s src tgt
                           .  ArchStmt arch (Value arch src)
                           -> Rewriter arch s src tgt ())
       -- ^ This rewrites an architecture specific statement
     , rewriteArchTermStmt :: (forall s src tgt . ArchTermStmt arch src
                                             -> Rewriter arch s src tgt (ArchTermStmt arch tgt))
       -- ^ This rewrites an architecture specific statement
     , archDemandContext :: !(DemandContext arch)
       -- ^ Provides architecture-specific information for computing which arguments must be
       -- evaluated when evaluating a statement.
     , postArchTermStmtAbsState :: !(forall ids
                                     .  Memory (ArchAddrWidth arch)
                                        -- The abstract state when block terminates.
                                     -> AbsBlockState (ArchReg arch)
                                        -- The registers before executing terminal statement
                                     -> (RegState (ArchReg arch) (Value arch ids))
                                        -- The architecture-specific statement
                                     -> ArchTermStmt arch ids
                                     -> Maybe (ArchSegmentOff arch, AbsBlockState (ArchReg arch)))
       -- ^ This takes an abstract state from before executing an abs
       -- state, and an architecture-specific terminal statement.
       --
       -- If the statement does not return to this function, this
       -- function should return `Nothing`.  Otherwise, it should
       -- returns the next address within the procedure that the
       -- statement jumps to along with the updated abstract state.
       --
       -- Note that per their documentation, architecture specific
       -- statements may return to at most one location within a
       -- function.
     }

-- | Apply optimizations to a terminal statement.
rewriteTermStmt :: ArchitectureInfo arch
                -> TermStmt arch src
                -> Rewriter arch s src tgt (TermStmt arch tgt)
rewriteTermStmt info tstmt = do
  case tstmt of
    FetchAndExecute regs ->
      FetchAndExecute <$> traverseF rewriteValue regs
    Branch c t f -> do
      tgtCond <- rewriteValue c
      case () of
        _ | Just (NotApp cn) <- valueAsApp tgtCond -> do
              pure $ Branch cn f t
          | otherwise ->
              pure $ Branch tgtCond t f
    TranslateError regs msg ->
      TranslateError <$> traverseF rewriteValue regs
                     <*> pure msg
    ArchTermStmt ts regs ->
      ArchTermStmt <$> rewriteArchTermStmt info ts
                   <*> traverseF rewriteValue regs

-- | Apply optimizations to code in the block
rewriteBlock :: ArchitectureInfo arch
             -> RewriteContext arch s src tgt
             -> Block arch src
             -> ST s (Block arch tgt)
rewriteBlock info rwctx b = do
  (tgtStmts, tgtTermStmt) <- runRewriter rwctx $ do
    mapM_ rewriteStmt (blockStmts b)
    rewriteTermStmt info (blockTerm b)
  -- Return new block
  pure $
    Block { blockLabel = blockLabel b
          , blockStmts = tgtStmts
          , blockTerm  = tgtTermStmt
          }
