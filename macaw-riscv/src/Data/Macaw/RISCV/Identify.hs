{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}

module Data.Macaw.RISCV.Identify where

import qualified GRIFT.Types as G
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Memory as MM
import qualified Data.Sequence as Seq

import           Control.Lens ((^.))
import           Control.Monad (guard)
import           Data.Maybe (isJust)
import           Data.Parameterized ( Some(..) )

import           Data.Macaw.RISCV.Arch
import           Data.Macaw.RISCV.RISCVReg

-- | The RISC-V ABI identifies x1 as the return address register. It
-- also identifies x5 as an "alternate" link register. It's not clear
-- whether that register is ever used in practice for other things,
-- but it seems probable that it is. Therefore, we probably don't want
-- to check that to identify a call site. We need to do some more
-- experimentation with gcc and llvm to see how x5 is used.
riscvIdentifyCall :: RISCVConstraints rv
                  => G.RVRepr rv
                  -> MM.Memory (MC.ArchAddrWidth (RISCV rv))
                  -> Seq.Seq (MC.Stmt (RISCV rv) ids)
                  -> MC.RegState (MC.ArchReg (RISCV rv)) (MC.Value (RISCV rv) ids)
                  -> Maybe (Seq.Seq (MC.Stmt (RISCV rv) ids), MC.ArchSegmentOff (RISCV rv))
riscvIdentifyCall _ mem stmts0 rs
  | not (null stmts0)
  , retVal@(MC.RelocatableValue {}) <- rs ^. MC.boundValue GPR_RA
  , Just retAddrVal <- MC.valueAsMemAddr retVal
  , Just retAddr <- MM.asSegmentOff mem retAddrVal =
      Just (stmts0, retAddr)
  | otherwise = Nothing

-- | To see if this block is executing a return, we check the
-- instruction pointer to see if it is equal to the abstract value
-- 'MC.ReturnAddr'.
riscvIdentifyReturn :: RISCVConstraints rv
                    => G.RVRepr rv
                    -> Seq.Seq (MC.Stmt (RISCV rv) ids)
                    -> MC.RegState (MC.ArchReg (RISCV rv)) (MC.Value (RISCV rv) ids)
                    -- ^ Register state after executing the block
                    -> MA.AbsProcessorState (MC.ArchReg (RISCV rv)) ids
                    -- ^ Abstract state at the start of the block
                    -> Maybe (Seq.Seq (MC.Stmt (RISCV rv) ids))
riscvIdentifyReturn rvRepr stmts0 rs absState = G.withRV rvRepr $ do
  Some MA.ReturnAddr <- matchReturn rvRepr absState (rs ^. MC.boundValue MC.ip_reg)
  return stmts0

-- FIXME: Right now, this code only works for RV64GC. We're going to
-- have to write it based on the rvRepr argument.
matchReturn :: RISCVConstraints rv
            => G.RVRepr rv
            -> MA.AbsProcessorState (MC.ArchReg (RISCV rv)) ids
            -> MC.Value (RISCV rv) ids (MT.BVType (MC.ArchAddrWidth (RISCV rv)))
            -> Maybe (Some (MA.AbsValue w))
matchReturn rvRepr absProcState ip = G.withRV rvRepr $ do
  MC.BVAnd _ addr (MC.BVValue _ mask) <- MC.valueAsApp ip
  let maskVal = case G.rvBaseArch rvRepr of
                  G.RV64Repr -> 0xfffffffffffffffe
                  G.RV32Repr -> 0xfffffffe
                  _ -> error ( "Unsupported base architecture: "
                            ++ (show (G.rvBaseArch rvRepr)))
  guard (mask == maskVal)
  case MA.transferValue absProcState addr of
    MA.ReturnAddr -> return (Some MA.ReturnAddr)
    _ -> Nothing

riscvCheckForReturnAddr :: RISCVConstraints rv
                        => G.RVRepr rv
                        -> MC.RegState (MC.ArchReg (RISCV rv)) (MC.Value (RISCV rv) ids)
                        -> MA.AbsProcessorState (MC.ArchReg (RISCV rv)) ids
                        -> Bool
riscvCheckForReturnAddr rvRepr r s = isJust $ matchReturn rvRepr s (r ^. MC.boundValue GPR_RA)
