{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.ElfEdit qualified as EE
import Data.Macaw.BinaryLoader.PPC ()
import Data.Macaw.Dump qualified as MD
import Data.Macaw.Memory.ElfLoader.PLTStubs qualified as MMEP
import Data.Macaw.PPC qualified as PPC
import Data.Macaw.PPC.Symbolic ()
import Data.Macaw.Symbolic qualified as MS
import Data.Proxy (Proxy(..))

main :: IO ()
main = do
  archVals <-
    case MS.archVals (Proxy @PPC.PPC32) Nothing of
      Just archVals -> pure archVals
      Nothing -> error "impossible"
  let pltStubInfo :: MMEP.PLTStubInfo EE.PPC32_RelocationType
      pltStubInfo = error "PLT stub discovery is not supported on PPC"
  MD.main PPC.ppc32_linux_info archVals pltStubInfo
