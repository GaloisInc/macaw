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
  , ReadAddrFn
  , DisassembleFn
  , archPostCallAbsState
  , archPostSyscallAbsState
  ) where

import Control.Monad.ST
import Data.Parameterized.Nonce

import Data.Macaw.AbsDomain.AbsState
import Data.Macaw.CFG
import Data.Macaw.Memory
import Data.Macaw.Types

------------------------------------------------------------------------
-- ArchitectureInfo

-- | A function for reading an address from memory
type ReadAddrFn w
   = MemSegment w
     -- ^ Segment to read from
   -> MemWord w
     -- Offset to read from.
   -> Either (MemoryError w) (MemWord w)

-- | Function for disassembling a block.
--
-- A block is defined as a contiguous region of code with a single known
-- entrance and potentially multiple exits.
--
-- This returns the list of blocks, one past the end of the last instruction successfully
-- disassembled, and any potential error that prematurely terminated translating the block.
type DisassembleFn arch
   = forall ids
   .  NonceGenerator (ST ids) ids
   -> Memory (ArchAddrWidth arch)
     -- ^ Segment to read from.
   -> (SegmentedAddr (ArchAddrWidth arch) -> Bool)
      -- ^ Predicate that given an offset, tells whether to continue reading given
      -- and offset in the segment.
   -> SegmentedAddr (ArchAddrWidth arch)
      -- ^ Segment that we are disassembling from
   -> AbsBlockState (ArchReg arch)
      -- ^ Abstract state associated with address that we are disassembling
      -- from.
      --
      -- This is used for things like the height of the x87 stack.
   -> ST ids ([Block arch ids], SegmentedAddr (ArchAddrWidth arch), Maybe String)

-- | This records architecture specific functions for analysis.
data ArchitectureInfo arch
   = ArchitectureInfo
     { archAddrWidth :: !(AddrWidthRepr (RegAddrWidth (ArchReg arch)))
       -- ^ Architecture address width.
     , jumpTableEntrySize :: !(MemWord (ArchAddrWidth arch))
       -- ^ The size of each entry in a jump table.
     , callStackDelta :: !Integer
       -- ^ The shift that the stack moves with a call.
     , disassembleFn :: !(DisassembleFn arch)
       -- ^ Function for disasembling a block.
     , preserveRegAcrossCall :: !(forall tp . ArchReg arch tp -> Bool)
       -- ^ Return true if architecture register should be preserved across a call.
     , preserveRegAcrossSyscall :: !(forall tp . ArchReg arch tp -> Bool)
       -- ^ Return true if architecture register should be preserved across a system call.
     , fnBlockStateFn :: !(Memory (RegAddrWidth (ArchReg arch))
                           -> SegmentedAddr (RegAddrWidth (ArchReg arch))
                           -> AbsBlockState (ArchReg arch))
       -- ^ Creates an abstract block state for representing the beginning of a
       -- function.
     , absEvalArchFn :: !(forall ids tp
                          .  AbsProcessorState (ArchReg arch) ids
                          -> ArchFn arch ids tp
                          -> AbsValue (RegAddrWidth (ArchReg arch)) tp)
       -- ^ Evaluates an architecture-specific function
     }

-- | Return state post call
archPostCallAbsState :: ( RegisterInfo (ArchReg arch)
                        , HasRepr (ArchReg arch) TypeRepr
                        )
                     => ArchitectureInfo arch
                        -- ^ Architecture information
                     -> AbsBlockState (ArchReg arch)
                     -> SegmentedAddr (RegAddrWidth (ArchReg arch))
                     -> AbsBlockState (ArchReg arch)
archPostCallAbsState archInfo = postCallAbsState params
  where params = CallParams { postCallStackDelta = negate (callStackDelta archInfo)
                            , preserveReg = preserveRegAcrossCall archInfo
                            }

-- | Return state post call
archPostSyscallAbsState :: ( RegisterInfo (ArchReg arch)
                           , HasRepr (ArchReg arch) TypeRepr
                           )
                        => ArchitectureInfo arch
                           -- ^ Architecture information
                        -> AbsBlockState (ArchReg arch)
                        -> SegmentedAddr (RegAddrWidth (ArchReg arch))
                        -> AbsBlockState (ArchReg arch)
archPostSyscallAbsState archInfo = postCallAbsState params
  where params = CallParams { postCallStackDelta = 0
                            , preserveReg = preserveRegAcrossSyscall archInfo
                            }
