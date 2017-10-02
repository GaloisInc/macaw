module Data.Macaw.PPC.Identify (
  identifyCall,
  identifyReturn
  ) where

import qualified Data.Sequence as Seq

import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM

identifyCall :: proxy ppc
             -> MM.Memory (ArchAddrWidth ppc)
             -> [Stmt ppc ids]
             -> RegState (ArchReg ppc) (Value ppc ids)
             -> Maybe (Seq.Seq (Stmt ppc ids), ArchSegmentOff ppc)
identifyCall = undefined

identifyReturn :: proxy ppc
               -> [Stmt ppc ids]
               -> RegState (ArchReg ppc) (Value ppc ids)
               -> Maybe [Stmt ppc ids]
identifyReturn = undefined
