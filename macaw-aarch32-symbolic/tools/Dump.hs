{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

-- Sometimes, GHC 9.4 is unable to find instances of RegAddrWidth that are
-- available by way of transitive module imports. The only reliable way of
-- preventing this issue that I've found is to import the defining module for
-- the instances (Data.Macaw.ARM.ARMReg) directly. See
-- https://gitlab.haskell.org/ghc/ghc/-/issues/16234 for the upstream GHC issue.
--
-- This issue does not affect GHC 9.6 or later, so when we drop support for GHC
-- 9.4, we can remove the redundant import below.
import Data.Macaw.ARM.ARMReg ()
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
