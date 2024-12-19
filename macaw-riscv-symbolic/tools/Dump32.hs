{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.Macaw.BinaryLoader.RISCV ()
import Data.Macaw.Dump qualified as MD
import Data.Macaw.RISCV qualified as MR
import Data.Macaw.RISCV.Symbolic ()
import Data.Macaw.Symbolic qualified as MS
import Data.Proxy (Proxy(..))
import GRIFT.Types qualified as G

main :: IO ()
main = do
  archVals <-
    case MS.archVals (Proxy @(MR.RISCV G.RV32GC)) Nothing of
      Just archVals -> pure archVals
      Nothing -> error "impossible"
  MD.main (MR.riscv_info G.rv32GCRepr) archVals MR.riscvPLTStubInfo
