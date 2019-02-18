module Main ( main ) where

import System.FilePath.Glob ( namesMatching )
import qualified Test.Tasty as T

import qualified PPC64Tests as PPC64
import qualified PPC64InstructionCoverage as PPC64

main :: IO ()
main = do
  testFiles <- namesMatching "tests/ppc/*.s.expected"
  bins <- namesMatching "tests/ppc/bin/*"
  T.defaultMain $ T.testGroup "PPCMacawTests" [
    PPC64.ppcAsmTests testFiles,
    PPC64.ppc64InstructionCoverageTests bins
    ]
