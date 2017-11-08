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

import           Data.Macaw.PPC.Arch
import           Data.Macaw.PPC.PPCReg
import           Data.Macaw.PPC.Simplify ( simplifyValue )

import           Debug.Trace (trace)


identifyCall :: (PPCArchConstraints ppc)
             => proxy ppc
             -> MM.Memory (MC.ArchAddrWidth ppc)
             -> [MC.Stmt ppc ids]
             -> MC.RegState (MC.ArchReg ppc) (MC.Value ppc ids)
             -> Maybe (Seq.Seq (MC.Stmt ppc ids), MC.ArchSegmentOff ppc)
identifyCall _ mem stmts0 rs
  | trace ("Identify call: " ++ unlines (map show stmts0)) False = undefined
  | not (null stmts0)
  , MC.AssignedValue (MC.Assignment { MC.assignRhs = MC.EvalApp app }) <- rs ^. MC.boundValue PPC_LNK
  , MC.BVAdd _ (MC.RelocatableValue {}) (MC.BVValue _ 0x4) <- app
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
