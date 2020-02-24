-- | Provides functions used to identify calls and returns in the instructions.

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Data.Macaw.ARM.Identify
    ( identifyCall
    , identifyReturn
    , isReturnValue
    ) where

import           Control.Lens ( (^.) )
import           Data.Macaw.ARM.Arch
import           Data.Macaw.AbsDomain.AbsState ( AbsProcessorState
                                               , AbsValue(..)
                                               , transferValue
                                               , ppAbsValue
                                               )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT
import           Data.Semigroup
import qualified Data.Sequence as Seq

import Prelude

-- import           Debug.Trace
debug :: Show a => a -> b -> b
-- debug = trace
debug = flip const


-- | Identifies a call statement, *after* the corresponding statement
-- has been performed.  This can be tricky with ARM because there are
-- several instructions that can update R15 and effect a "call",
-- athough the predicate condition on those instructions can determine
-- if it is actually executed or not.  Also need to consider A32
-- v.s. T32 mode.
identifyCall :: ARMArchConstraints arm =>
                proxy arm
             -> MM.Memory (MC.ArchAddrWidth arm)
             -> Seq.Seq (MC.Stmt arm ids)
             -> MC.RegState (MC.ArchReg arm) (MC.Value arm ids)
             -> Maybe (Seq.Seq (MC.Stmt arm ids), MC.ArchSegmentOff arm)
identifyCall _ _mem _stmts0 _rs = Nothing  -- KWQ: for now, nothing is identified as a call


-- | Intended to identify a return statement.
--
-- The current implementation is to attempt to recognize the Macaw
-- 'ReturnAddr' value (placed in the LR register by
-- 'mkInitialAbsState') when it is placed in the PC (instruction
-- pointer), but unfortunately this does not work because ARM
-- semantics will clear the low bit (T32 mode) or the low two bits
-- (A32 mode) when writing to the PC to discard the mode bit in target
-- addresses.
identifyReturn :: ARMArchConstraints arm =>
                  proxy arm
               -> Seq.Seq (MC.Stmt arm ids)
               -> MC.RegState (MC.ArchReg arm) (MC.Value arm ids)
               -> AbsProcessorState (MC.ArchReg arm) ids
               -> Maybe (Seq.Seq (MC.Stmt arm ids))
identifyReturn arm stmts s finalRegSt8 =
  if isReturnValue arm finalRegSt8 (s^.MC.boundValue MC.ip_reg)
  then Just stmts
  else Nothing


-- | Determines if the supplied value is the symbolic return address
-- from Macaw, modulo any ARM semantics operations (lots of ite caused
-- by the conditional execution bits for most instructions, clearing
-- of the low bits (1 in T32 mode, 2 in A32 mode).
isReturnValue :: ARMArchConstraints arm =>
                 proxy arm
              -> AbsProcessorState (MC.ArchReg arm) ids
              -> MC.Value arm ids (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
              -> Bool
isReturnValue _ absProcState val =
  case transferValue absProcState val of
    ReturnAddr -> True
    -- TBD: fill in the code here to recognize the expression that
    -- clears the lower bit(s), along the lines of what is done by PPC
    -- Identify.hs for the shifting operations.
    o -> debug ("######################## Unrecognized return value: " <>
                show (MC.ppValue 0 val) <>
                " or " <>
                show (ppAbsValue o)
               ) False
