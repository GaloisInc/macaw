module Main ( main ) where

import System.FilePath.Glob ( namesMatching )
import qualified Test.Tasty as T

import qualified RISCVTests as RISCV

main :: IO ()
main = do
  testFiles <- namesMatching "tests/riscv/*.expected"
  bins <- namesMatching "tests/riscv/bin/*"
  print testFiles
  T.defaultMain $ T.testGroup "RISCVMacawTests" [
    RISCV.riscvAsmTests testFiles
    -- RISCV.riscvInstructionCoverageTests bins
    ]
