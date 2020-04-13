module Data.Macaw.RISCV.Identify where

import qualified GRIFT.Types as G
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Sequence as Seq

riscvIdentifyCall :: G.RVRepr rv
                  -> MM.Memory (MC.ArchAddrWidth rv)
                  -> Seq.Seq (MC.Stmt rv ids)
                  -> MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
                  -> Maybe (Seq.Seq (MC.Stmt rv ids), MC.ArchSegmentOff rv)
riscvIdentifyCall _ _ _ _ = undefined
