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
-- This returns the list of blocks, the number of bytes in the blocks,
-- and any potential error that prematurely terminated translating the
-- block.
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
     , callStackDelta :: !Integer
       -- ^ The shift that the stack moves with a call.
     , disassembleFn :: !(DisassembleFn arch)
       -- ^ Function for disasembling a block.
     , preserveRegAcrossCall :: !(forall tp . ArchReg arch tp -> Bool)
       -- ^ Return true if architecture register should be preserved across a call.
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
     }

-- | Return state post call
archPostCallAbsState :: ArchitectureInfo arch
                        -- ^ Architecture information
                     -> AbsBlockState (ArchReg arch)
                     -> SegmentedAddr (RegAddrWidth (ArchReg arch))
                     -> AbsBlockState (ArchReg arch)
archPostCallAbsState info = withArchConstraints info $
  let params = CallParams { postCallStackDelta = negate (callStackDelta info)
                          , preserveReg = preserveRegAcrossCall info
                          }
   in postCallAbsState params

-- | Return state post call
archPostSyscallAbsState :: ArchitectureInfo arch
                           -- ^ Architecture information
                        -> AbsBlockState (ArchReg arch)
                        -> SegmentedAddr (RegAddrWidth (ArchReg arch))
                        -> AbsBlockState (ArchReg arch)
archPostSyscallAbsState info = withArchConstraints info $ postCallAbsState params
  where params = CallParams { postCallStackDelta = 0
                            , preserveReg = preserveRegAcrossSyscall info
                            }
