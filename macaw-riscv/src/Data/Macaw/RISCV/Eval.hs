{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Data.Macaw.RISCV.Eval
  ( riscvInitialBlockRegs
  , riscvInitialAbsState
  , riscvCallParams
  , riscvAddrWidth
  ) where

import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import qualified GRIFT.Types as G

import Control.Lens ((.~), (&))

import Data.Macaw.RISCV.Arch
import Data.Macaw.RISCV.RISCVReg

-- | At the beginning of each block, the PC holds the address of the block.
riscvInitialBlockRegs :: RISCVConstraints rv
                      => G.RVRepr rv
                      -> MC.ArchSegmentOff rv
                      -> MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
riscvInitialBlockRegs rvRepr startIP = G.withRV rvRepr $
  MC.mkRegState MC.Initial &
  MC.curIP .~ MC.RelocatableValue (riscvAddrWidth rvRepr) (MM.segoffAddr startIP)

-- | At the beginning of each function, GPR_RA holds the return address.
riscvInitialAbsState :: RISCVConstraints rv
                     => G.RVRepr rv
                     -> MM.Memory (MC.ArchAddrWidth rv)
                     -> MC.ArchSegmentOff rv
                     -> MA.AbsBlockState (MC.ArchReg rv)
riscvInitialAbsState rvRepr _mem startAddr = s0
  where
    initRegVals = MapF.fromList [ MapF.Pair GPR_RA MA.ReturnAddr ]
    s0 = G.withRV rvRepr $ MA.fnStartAbsBlockState startAddr initRegVals []

riscvCallParams :: MA.CallParams (RISCVReg rv)
riscvCallParams = MA.CallParams { MA.postCallStackDelta = 0
                                , MA.preserveReg = riscvPreserveReg
                                , MA.stackGrowsDown = True
                                }

riscvPreserveReg :: RISCVReg rv tp -> Bool
riscvPreserveReg GPR_SP = True
riscvPreserveReg GPR_S0 = True
riscvPreserveReg GPR_S1 = True
riscvPreserveReg GPR_S2 = True
riscvPreserveReg GPR_S3 = True
riscvPreserveReg GPR_S4 = True
riscvPreserveReg GPR_S5 = True
riscvPreserveReg GPR_S6 = True
riscvPreserveReg GPR_S7 = True
riscvPreserveReg GPR_S8 = True
riscvPreserveReg GPR_S9 = True
riscvPreserveReg GPR_S10 = True
riscvPreserveReg GPR_S11 = True
riscvPreserveReg (FPR rid)
  | rid == 8 = True
  | rid == 9 = True
  | rid >= 18 && rid <= 27 = True
riscvPreserveReg _ = False

riscvAddrWidth :: G.RVRepr rv
               -> MM.AddrWidthRepr (MC.ArchAddrWidth rv)
riscvAddrWidth rvRepr = case G.rvBaseArch rvRepr of
  G.RV32Repr -> MM.Addr32
  G.RV64Repr -> MM.Addr64
  G.RV128Repr -> error "RV128 not supported"
