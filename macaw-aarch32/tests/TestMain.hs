module Main where


import ARMTests
import MismatchTests
import System.FilePath.Glob (namesMatching)
import Test.Tasty (defaultMain, testGroup)


main :: IO ()
main = do
  testFiles <- namesMatching "tests/arm/*.mcw.expected"
  _bins <- namesMatching "tests/arm/bin/*"
  badbins <- namesMatching "tests/arm/*.exe=bad"
  defaultMain $ testGroup "ARMMacawTests"
                  [ armAsmTests testFiles
                  , armMismatchTests badbins
                  ]
