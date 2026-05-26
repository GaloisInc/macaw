module Main (main) where

import qualified Test.Tasty as TT
import           Test.Tasty.HUnit ( assertBool, testCase )

import Data.Macaw.Internal ( assertionsEnabled )

import qualified AbsDomain.AbsValueTests as AbsValue
import qualified AbsDomain.FinSetTests as FinSet
import qualified AbsDomain.Gen as Gen
import qualified AbsDomain.JumpBoundsTests as JumpBounds
import qualified AbsDomain.SolveDiophantineTests as SolveDio
import qualified AbsDomain.StridedIntervalTests as SI

main :: IO ()
main = TT.defaultMain $
  TT.testGroup "macaw-base"
    [ -- See Note [Asserts] in Data.Macaw.Internal
      testCase "assertions enabled" $ do
        assertsEnabled <- assertionsEnabled
        assertBool "assertions should be enabled" assertsEnabled
    , Gen.tests
    , SolveDio.tests
    , SI.tests
    , FinSet.tests
    , AbsValue.tests
    , JumpBounds.tests
    ]
