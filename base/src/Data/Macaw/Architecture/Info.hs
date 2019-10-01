{-|
This defines the architecture-specific information needed for code discovery.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Macaw.Architecture.Info
  ( ArchitectureInfo(..)
  , postCallAbsState
  , ArchBlockPrecond
  , DisassembleFn
  , IntraJumpTarget
    -- * Unclassified blocks
  , module Data.Macaw.CFG.Block
  , rewriteBlock
  ) where

import           Control.Monad.ST
import qualified Data.Kind as K
import           Data.Parameterized.Nonce
import           Data.Parameterized.TraversableF
import           Data.Sequence (Seq)

import           Data.Macaw.AbsDomain.AbsState as AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import           Data.Macaw.CFG.Block
import           Data.Macaw.CFG.Core
import           Data.Macaw.CFG.DemandSet
import           Data.Macaw.CFG.Rewriter
import           Data.Macaw.Memory

------------------------------------------------------------------------
-- ArchitectureInfo

-- | This family maps architecture parameters to information needed to
-- successfully translate machine code into Macaw CFGs.
--
-- This is currently used for registers values that are required to be
-- known constants at translation time.  For example, on X86_64, due to
-- aliasing between the FPU and MMX registers, we require that the
-- floating point stack value is known at translation time so that
-- we do not need to check which register is modified when pushing or
-- poping from the x86 stack.
--
-- If no preconditions are needed, this can just be set to the unit type.
type family ArchBlockPrecond (arch :: K.Type) :: K.Type

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
   -> ST s (Block arch ids, Int)

type IntraJumpTarget arch =
  (MemSegmentOff (ArchAddrWidth arch), AbsBlockState (ArchReg arch), Jmp.InitJumpBounds arch)
-- ^ Identifies address we are jumping to an abstract state/bounds for getting there.

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
     , extractBlockPrecond :: !(ArchSegmentOff arch
                                -> AbsBlockState (ArchReg arch)
                                -> Either String (ArchBlockPrecond arch))
       -- ^ Attempt to use abstract domain information to extract
       -- information needed to translate block.
     , initialBlockRegs :: !(forall ids
                             .  ArchSegmentOff arch
                             -> ArchBlockPrecond arch
                             -> RegState (ArchReg arch) (Value arch ids))
       -- ^ Create initial registers from address and precondition.
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
     , archCallParams :: !(CallParams (ArchReg arch))
       -- ^ Update the abstract state after a function call returns

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
     , postArchTermStmtAbsState :: !(forall ids s
                                     .  Memory (ArchAddrWidth arch)
                                        -- The abstract state when block terminates.
                                     -> AbsProcessorState (ArchReg arch) ids
                                        -- The registers before executing terminal statement
                                     -> Jmp.IntraJumpBounds arch ids s
                                     -> RegState (ArchReg arch) (Value arch ids)
                                        -- The architecture-specific statement
                                     -> ArchTermStmt arch ids
                                     -> Maybe (IntraJumpTarget arch))
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

postCallAbsState :: ArchitectureInfo arch
                 -> AbsProcessorState (ArchReg arch) ids
                 -- ^ Processor state at call.
                 -> RegState (ArchReg arch) (Value arch ids)
                 -- ^  Register values when call occurs.
                 -> ArchSegmentOff arch
                 -- ^ Return address
                 -> AbsBlockState (ArchReg arch)
postCallAbsState ainfo = withArchConstraints ainfo $
  absEvalCall (archCallParams ainfo)

-- | Apply optimizations to a terminal statement.
rewriteTermStmt :: ArchitectureInfo arch
                -> TermStmt arch src
                -> Rewriter arch s src tgt (TermStmt arch tgt)
rewriteTermStmt info tstmt = do
  case tstmt of
    FetchAndExecute regs ->
      FetchAndExecute <$> traverseF rewriteValue regs
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
             -> ST s (RewriteContext arch s src tgt, Block arch tgt)
rewriteBlock info rwctx b = do
  (rwctx', tgtStmts, tgtTermStmt) <- runRewriter rwctx $ do
    mapM_ rewriteStmt (blockStmts b)
    rewriteTermStmt info (blockTerm b)
  -- Return rewritten block and any new blocks
  let rwBlock = Block { blockStmts = tgtStmts
                      , blockTerm  = tgtTermStmt
                      }
  pure (rwctx', rwBlock)
