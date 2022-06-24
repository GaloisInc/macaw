{-# LANGUAGE TypeApplications #-}
module Main ( main ) where

import           Data.Proxy ( Proxy(..) )
import           System.FilePath.Glob ( namesMatching )
import qualified Test.Tasty as T
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR

import qualified ElfX64Linux as T


ingredients :: [TTR.Ingredient]
ingredients = T.includingOptions [ TTO.Option (Proxy @T.SaveMacaw)
                                 ] : T.defaultIngredients

main :: IO ()
main = do
  x64AsmTests <- namesMatching "tests/x64/*.expected"
  T.defaultMainWithIngredients ingredients $ T.testGroup "ReoptTests" [
    T.elfX64LinuxTests x64AsmTests
    ]
