module Main where


-- import qualified ARMTest as ARM
import           System.FilePath.Glob ( namesMatching )
import           Test.Tasty (defaultMain, testGroup)


main :: IO ()
main = do
  testFiles <- namesMatching "tests/arm/*.s.expected"
  bins <- namesMatching "tests/arm/bin/*"
  defaultMain $ testGroup "ARMMacawTests" [
    -- ARM.armAsmTests testFiles,
    -- ARM.armInstructionCoverageTests bins
    ]
