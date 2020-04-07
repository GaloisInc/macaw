{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Data.Macaw.RISCV.Eval
  ( riscvInitialBlockRegs
  , riscvInitialAbsState
  ) where

import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import qualified GRIFT.Types as GT

import Control.Lens ((.~), (&))

import Data.Macaw.RISCV.RISCVReg

riscvInitialBlockRegs :: RISCV rv
                      => GT.RVRepr rv
                      -> MC.ArchSegmentOff rv
                      -> MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
riscvInitialBlockRegs rvRepr startIP = MC.mkRegState MC.Initial &
  MC.curIP .~ MC.RelocatableValue (riscvAddrWidth rvRepr) (MM.segoffAddr startIP)

riscvInitialAbsState :: RISCV rv
                     => GT.RVRepr rv
                     -> MM.Memory (MC.RegAddrWidth (MC.ArchReg rv))
                     -> MC.ArchSegmentOff rv
                     -> MA.AbsBlockState (MC.ArchReg rv)
riscvInitialAbsState _rvRepr _mem startAddr = s0
  where
    initRegVals = MapF.fromList [ MapF.Pair ra MA.ReturnAddr ]
    s0 = MA.fnStartAbsBlockState startAddr initRegVals []
