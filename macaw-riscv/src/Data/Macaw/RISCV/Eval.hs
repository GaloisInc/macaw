{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Data.Macaw.RISCV.Eval
  ( riscvInitialBlockRegs
  ) where

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified GRIFT.Types as GT

import Control.Lens ((.~), (&))

import Data.Macaw.RISCV.RISCVReg

riscvInitialBlockRegs :: RISCV rv
                      => GT.RVRepr rv
                      -> MC.ArchSegmentOff rv
                      -> MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
riscvInitialBlockRegs rvRepr startIP = MC.mkRegState MC.Initial &
  MC.curIP .~ MC.RelocatableValue (riscvAddrWidth rvRepr) (MM.segoffAddr startIP)
