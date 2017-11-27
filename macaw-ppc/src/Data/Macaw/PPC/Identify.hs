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

import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg

import           Debug.Trace (trace)

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
  | trace ("Identify call: " ++ unlines (map show stmts0)) False = undefined
  | not (null stmts0)
  , MC.RelocatableValue {} <- rs ^. MC.boundValue PPC_LNK
  , Just retVal <- simplifyValue (rs ^. MC.boundValue PPC_LNK)
  , Just retAddrVal <- MC.asLiteralAddr retVal
  , Just retAddr <- MM.asSegmentOff mem retAddrVal =
      Just (Seq.fromList stmts0, retAddr)
  | otherwise = Nothing

identifyReturn :: (PPCArchConstraints ppc)
               => proxy ppc
               -> [MC.Stmt ppc ids]
               -> MC.RegState (MC.ArchReg ppc) (MC.Value ppc ids)
               -> Maybe [MC.Stmt ppc ids]
identifyReturn _ = undefined
