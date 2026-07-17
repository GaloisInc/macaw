{-# LANGUAGE TypeApplications #-}
module Main where


import ARMTests
import MismatchTests
import Data.Proxy ( Proxy(..) )
import System.FilePath.Glob (glob)
import qualified Test.Tasty as TT
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR
import qualified Relocs

ingredients :: [TTR.Ingredient]
ingredients = TT.includingOptions [ TTO.Option (Proxy @SaveMacaw)
                                  ] : TT.defaultIngredients

main :: IO ()
main = do
  testFiles <- glob "tests/arm/*.mcw.expected"
  _bins <- glob "tests/arm/bin/*"
  badbins <- glob "tests/arm/*.exe=bad"
  relocsTests <- Relocs.tests
  TT.defaultMainWithIngredients ingredients $ TT.testGroup "ARMMacawTests"
                  [ armAsmTests testFiles
                  , armMismatchTests badbins
                  , relocsTests
                  ]
