{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.Macaw.AArch32.Symbolic ()
import Data.Macaw.ARM qualified as MA
import Data.Macaw.Dump qualified as MD
import Data.Macaw.Symbolic qualified as MS
import Data.Proxy (Proxy(..))

main :: IO ()
main = do
  archVals <-
    case MS.archVals (Proxy @MA.ARM) Nothing of
      Just archVals -> pure archVals
      Nothing -> error "impossible"
  MD.main MA.arm_linux_info archVals MA.armPLTStubInfo
