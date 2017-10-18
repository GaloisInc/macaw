module Main ( main ) where

import qualified Test.Tasty as T

main :: IO ()
main = T.defaultMain tests

tests :: T.TestTree
tests = T.testGroup "PPC Tests" []

