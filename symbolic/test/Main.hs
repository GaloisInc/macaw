module Main (main) where

import Test.Tasty ( defaultMain, testGroup )
import Test.Tasty.HUnit ( assertBool, testCase )

import Data.Macaw.Symbolic.Internal ( assertionsEnabled )

main :: IO ()
main = defaultMain $ testGroup "macaw-symbolic"
  [ -- See Note [Asserts] in Data.Macaw.Symbolic.Internal
    testCase "assertions enabled" $ do
      assertsEnabled <- assertionsEnabled
      assertBool "assertions should be enabled" assertsEnabled
  ]
