module Main (main) where

import Test.Tasty ( defaultMain )
import Test.Tasty.HUnit ( assertBool, testCase )

import Data.Macaw.Internal ( assertionsEnabled )

main :: IO ()
main = defaultMain $
  -- See Note [Asserts] in Data.Macaw.Internal
  testCase "assertions enabled" $ do
    assertsEnabled <- assertionsEnabled
    assertBool "assertions should be enabled" assertsEnabled
