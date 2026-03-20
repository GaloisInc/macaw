{-# LANGUAGE TypeApplications #-}
module Main ( main ) where

import           Data.Macaw.X86.Internal ( assertionsEnabled )
import           Data.Proxy ( Proxy(..) )
import           System.FilePath.Glob ( namesMatching )
import qualified Test.Tasty as T
import qualified Test.Tasty.HUnit as TTH
import qualified Test.Tasty.Options as TTO
import qualified Test.Tasty.Runners as TTR

import qualified ElfX64Linux as T


ingredients :: [TTR.Ingredient]
ingredients = T.includingOptions [ TTO.Option (Proxy @T.SaveMacaw)
                                 ] : T.defaultIngredients

main :: IO ()
main = do
  x64AsmTests <- namesMatching "tests/x64/*.expected"
  T.defaultMainWithIngredients ingredients $ T.testGroup "ReoptTests"
    [ T.elfX64LinuxTests x64AsmTests
    -- See Note [Asserts] in Data.Macaw.X86.Internal
    , TTH.testCase "assertions enabled" $ do
        assertsEnabled <- assertionsEnabled
        TTH.assertBool "assertions should be enabled" assertsEnabled
    ]
