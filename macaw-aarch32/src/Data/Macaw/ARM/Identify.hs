-- | Provides functions used to identify calls and returns in the instructions.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.ARM.Identify
    ( identifyCall
    , identifyReturn
    , isReturnValue
    ) where

import           Control.Lens ( (^.) )
import           Control.Monad ( guard )
import qualified Data.Macaw.ARM.ARMReg as AR
import           Data.Macaw.AbsDomain.AbsState ( AbsProcessorState
                                               , AbsValue(..)
                                               , transferValue
                                               , ppAbsValue
                                               , absAssignments
                                               , AbsBlockStack
                                               , ppAbsStack
                                               , curAbsStack
                                               )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Simplify as MSS
import qualified Data.Macaw.Types as MT
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Semigroup
import qualified Data.Sequence as Seq

import qualified SemMC.Architecture.AArch32 as ARM

import           Data.Macaw.ARM.Simplify ()

import Prelude

import qualified Language.ASL.Globals as ASL
import           Text.Printf ( printf )
import           Debug.Trace
debug :: Show a => a -> b -> b
-- debug = trace
debug = flip const


-- | Identifies a call statement, *after* the corresponding statement
-- has been performed.  This can be tricky with ARM because there are
-- several instructions that can update R15 and effect a "call",
-- athough the predicate condition on those instructions can determine
-- if it is actually executed or not.  Also need to consider A32
-- v.s. T32 mode.
identifyCall :: MM.Memory (MC.ArchAddrWidth ARM.AArch32)
             -> Seq.Seq (MC.Stmt ARM.AArch32 ids)
             -> MC.RegState (MC.ArchReg ARM.AArch32) (MC.Value ARM.AArch32 ids)
             -> Maybe (Seq.Seq (MC.Stmt ARM.AArch32 ids), MC.ArchSegmentOff ARM.AArch32)
identifyCall mem stmts0 rs
  | not (null stmts0)
  , MC.RelocatableValue {} <- rs ^. MC.boundValue AR.arm_LR
  , Just retVal <- MSS.simplifyValue (rs ^. MC.boundValue AR.arm_LR)
  , Just retAddrVal <- MC.valueAsMemAddr retVal
  , Just retAddr <- MM.asSegmentOff mem retAddrVal =
      Just (stmts0, retAddr)
  | otherwise = Nothing

-- | Intended to identify a return statement.
--
-- The current implementation is to attempt to recognize the Macaw
-- 'ReturnAddr' value (placed in the LR register by
-- 'mkInitialAbsState') when it is placed in the PC (instruction
-- pointer), but unfortunately this does not work because ARM
-- semantics will clear the low bit (T32 mode) or the low two bits
-- (A32 mode) when writing to the PC to discard the mode bit in target
-- addresses.
identifyReturn :: Seq.Seq (MC.Stmt ARM.AArch32 ids)
               -> MC.RegState (MC.ArchReg ARM.AArch32) (MC.Value ARM.AArch32 ids)
               -> AbsProcessorState (MC.ArchReg ARM.AArch32) ids
               -> Maybe (Seq.Seq (MC.Stmt ARM.AArch32 ids))
identifyReturn stmts s finalRegSt8 =
  trace (printf "IP=%s (abstract=%s)" (show ipval) (show ipabs)) $
  trace (showAbs (finalRegSt8 ^. absAssignments) (finalRegSt8 ^. curAbsStack)) $
  if isReturnValue finalRegSt8 (s^.MC.boundValue MC.ip_reg)
  then Just stmts
  else Nothing
  where
    ipval = s ^. MC.boundValue MC.ip_reg
    ipabs = transferValue finalRegSt8 ipval

showAbs :: MapF.MapF (MC.AssignId ids) (AbsValue 32)
        -> AbsBlockStack 32
        -> String
showAbs m stk = unlines ( "Abs State:"
                        : fmap showPair (MapF.toList m)
                        ) ++ show (ppAbsStack stk)
  where
    showPair :: MapF.Pair (MC.AssignId ids) (AbsValue 32) -> String
    showPair (MapF.Pair aid absv) = printf "%s: %s" (show aid) (show absv)

-- | Determines if the supplied value is the symbolic return address
-- from Macaw, modulo any ARM semantics operations (lots of ite caused
-- by the conditional execution bits for most instructions, clearing
-- of the low bits (1 in T32 mode, 2 in A32 mode).
isReturnValue :: AbsProcessorState (MC.ArchReg ARM.AArch32) ids
              -> MC.Value ARM.AArch32 ids (MT.BVType (MC.RegAddrWidth (MC.ArchReg ARM.AArch32)))
              -> Bool
isReturnValue absProcState val =
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

