{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
module Data.Macaw.PPC.Identify (
  identifyCall,
  identifyReturn
  ) where

import qualified Data.Sequence as Seq

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM

import           Data.Macaw.PPC.PPCReg

import Debug.Trace (trace)
import Data.List (intercalate)

identifyCall :: MC.ArchConstraints ppc
             => proxy ppc
             -> MM.Memory (MC.ArchAddrWidth ppc)
             -> [MC.Stmt ppc ids]
             -> MC.RegState (MC.ArchReg ppc) (MC.Value ppc ids)
             -> Maybe (Seq.Seq (MC.Stmt ppc ids), MC.ArchSegmentOff ppc)
identifyCall _ mem stmts rs = trace ("identifyCall:\n\n" ++
                                     intercalate "\n" (map show stmts))
                              Nothing

identifyReturn :: (PPCWidth ppc)
               => proxy ppc
               -> [MC.Stmt ppc ids]
               -> MC.RegState (MC.ArchReg ppc) (MC.Value ppc ids)
               -> Maybe [MC.Stmt ppc ids]
identifyReturn _ = undefined
