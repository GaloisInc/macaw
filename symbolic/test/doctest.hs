module Main ( main ) where

import qualified Test.DocTest as T

main :: IO ()
main = T.doctest ["-isrc", "src/Data/Macaw/Symbolic.hs", "src/Data/Macaw/Symbolic/Memory.hs"]
