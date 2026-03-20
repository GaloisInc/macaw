{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE TypeApplications #-}

-- | Items in this module should /not/ be considered part of macaw-x86's
-- API, they are exported only for the sake of the test suite.
module Data.Macaw.X86.Internal
  ( assertionsEnabled
  ) where

import qualified Control.Exception as X
import           Data.Functor ((<&>))

-- | Check if assertions are enabled.
--
-- Note [Asserts]: When optimizations are enabled, GHC compiles 'X.assert' to
-- a no-op. However, Cabal enables @-O1@ by default. Therefore, if we want our
-- assertions to be checked by our test suite, we must carefully ensure that we
-- pass the correct flags to GHC for the @lib:macaw-x86@ target. We verify
-- that we have done so by asserting as much in the test suite.
--
-- See also:
--
-- * @cabal.project.werror@ for the @-fno-ignore-asserts@ flag
assertionsEnabled :: IO Bool
assertionsEnabled = do
  X.try @X.AssertionFailed (X.assert False (pure ())) <&>
    \case
      Left _ -> True
      Right () -> False
