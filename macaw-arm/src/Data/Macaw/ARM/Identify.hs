-- | Provides functions used to identify calls and returns in the instructions.

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Data.Macaw.ARM.Identify
    ( identifyCall
    , identifyReturn
    ) where

import           Control.Lens ( (^.) )
import           Data.Macaw.ARM.Arch
import           Data.Macaw.AbsDomain.AbsState ( AbsProcessorState
                                               , AbsValue(..)
                                               , transferValue
                                               )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Sequence as Seq


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
identifyReturn _ stmts s finalRegSt8 =
    case transferValue finalRegSt8 (s^.MC.boundValue MC.ip_reg) of
      ReturnAddr -> Just stmts
      _ -> Nothing
