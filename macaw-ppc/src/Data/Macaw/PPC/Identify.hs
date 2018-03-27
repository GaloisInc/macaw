{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
module Data.Macaw.PPC.Identify (
  identifyCall,
  identifyReturn
  ) where

import           Control.Lens ( (^.) )
import qualified Data.Sequence as Seq

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.AbsDomain.AbsState ( AbsProcessorState
                                               , AbsValue(..)
                                               , transferValue
                                               )

import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg

-- | Our current heuristic is that we are issuing a (potentially conditional)
-- call if we see an address in the link register.
--
-- This seems reasonable, as the only time the link register would be populated
-- with a constant is at a call site.  This might be a problem if we see a
-- @mtlr@ and put a stack value into the link register.  That might look like a
-- call...
identifyCall :: (PPCArchConstraints ppc)
             => proxy ppc
             -> MM.Memory (MC.ArchAddrWidth ppc)
             -> [MC.Stmt ppc ids]
             -> MC.RegState (MC.ArchReg ppc) (MC.Value ppc ids)
             -> Maybe (Seq.Seq (MC.Stmt ppc ids), MC.ArchSegmentOff ppc)
identifyCall _ mem stmts0 rs
  | not (null stmts0)
  , MC.RelocatableValue {} <- rs ^. MC.boundValue PPC_LNK
  , Just retVal <- simplifyValue (rs ^. MC.boundValue PPC_LNK)
  , Just retAddrVal <- MC.asLiteralAddr retVal
  , Just retAddr <- MM.asSegmentOff mem retAddrVal =
      Just (Seq.fromList stmts0, retAddr)
  | otherwise = Nothing


-- | Called to determine if the instruction sequence contains a return
-- from the current function.
--
-- An instruction executing a return from a function will place the
-- Macaw 'ReturnAddr' value (placed in the LNK register by
-- 'mkInitialAbsState') into the instruction pointer.
identifyReturn :: (PPCArchConstraints ppc) =>
                  proxy ppc
               -> [MC.Stmt ppc ids]
               -> MC.RegState (MC.ArchReg ppc) (MC.Value ppc ids)
               -> AbsProcessorState (MC.ArchReg ppc) ids
               -> Maybe (Seq.Seq (MC.Stmt ppc ids))
identifyReturn _ stmts s finalRegSt8 =
    case transferValue finalRegSt8 (s^.MC.boundValue PPC_IP) of
      ReturnAddr -> Just $ Seq.fromList stmts
      _ -> Nothing
