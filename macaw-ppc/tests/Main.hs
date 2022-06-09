{-# LANGUAGE TypeApplications #-}
module Main ( main ) where

import           Data.Proxy ( Proxy(..) )
import           System.FilePath.Glob ( namesMatching )
import qualified Test.Tasty as T
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR

import qualified PPCTests as PPC
import qualified PPC64InstructionCoverage as PPC64

ingredients :: [TTR.Ingredient]
ingredients = T.includingOptions [ TTO.Option (Proxy @PPC.SaveMacaw)
                                 ] : T.defaultIngredients


main :: IO ()
main = do
  testFiles64 <- namesMatching "tests/ppc64/*.s.expected"
  testFiles32 <- namesMatching "tests/ppc32/*.s.expected"
  bins <- namesMatching "tests/ppc64/bin/*"
  T.defaultMainWithIngredients ingredients $ T.testGroup "PPCMacawTests" [
    PPC.ppcAsmTests "PPC64" testFiles64,
    PPC.ppcAsmTests "PPC32" testFiles32,
    PPC64.ppc64InstructionCoverageTests bins
    ]
