module Main ( main ) where

import System.FilePath.Glob ( glob )
import qualified Test.Tasty as T

import qualified RISCVTests as RISCV
import qualified Relocs

main :: IO ()
main = do
  testFiles <- glob "tests/riscv/*.expected"
  relocsTests <- Relocs.tests
  print testFiles
  T.defaultMain $ T.testGroup "RISCVMacawTests" [
    RISCV.riscvAsmTests testFiles,
    relocsTests
    ]
