{-# LANGUAGE TypeApplications #-}
module Main where


import ARMTests
import MismatchTests
import Data.Proxy ( Proxy(..) )
import System.FilePath.Glob (namesMatching)
import qualified Test.Tasty as TT
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR

ingredients :: [TTR.Ingredient]
ingredients = TT.includingOptions [ TTO.Option (Proxy @SaveMacaw)
                                  ] : TT.defaultIngredients

main :: IO ()
main = do
  testFiles <- namesMatching "tests/arm/*.mcw.expected"
  _bins <- namesMatching "tests/arm/bin/*"
  badbins <- namesMatching "tests/arm/*.exe=bad"
  TT.defaultMainWithIngredients ingredients $ TT.testGroup "ARMMacawTests"
                  [ armAsmTests testFiles
                  , armMismatchTests badbins
                  ]
