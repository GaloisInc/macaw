-- | Provides functions used to identify calls and returns in the instructions.

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Data.Macaw.ARM.Identify
    ( identifyCall
    , identifyReturn
    ) where

import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch
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
             -> [MC.Stmt arm ids]
             -> MC.RegState (MC.ArchReg arm) (MC.Value arm ids)
             -> Maybe (Seq.Seq (MC.Stmt arm ids), MC.ArchSegmentOff arm)
identifyCall _ mem stmts0 rs = Nothing  -- KWQ: for now, nothing is identified as a call


-- | Intended to identify a return statement.  Currently appears to be unused.
identifyReturn :: ARMArchConstraints arm =>
                  proxy ppc
               -> [MC.Stmt arm ids]
               -> MC.RegState (MC.ArchReg arm) (MC.Value arm ids)
               -> Maybe [MC.Stmt arm ids]
identifyReturn _ = error "ARM identifyReturn is TBD"
