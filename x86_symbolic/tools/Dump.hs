{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.Macaw.BinaryLoader.X86 ()
import Data.Macaw.Dump qualified as MD
import Data.Macaw.Symbolic qualified as MS
import Data.Macaw.X86 qualified as MX
import Data.Macaw.X86.Symbolic ()
import Data.Proxy (Proxy(..))

main :: IO ()
main = do
  archVals <-
    case MS.archVals (Proxy @MX.X86_64) Nothing of
      Just archVals -> pure archVals
      Nothing -> error "impossible"
  MD.main MX.x86_64_linux_info archVals MX.x86_64PLTStubInfo
