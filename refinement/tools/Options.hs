module Options (
  Options(..)
  ) where

import qualified Data.Macaw.Refinement as MR

data Options = Options { inputFile :: FilePath
                       , unrefined :: Bool
                       , summaryOnly :: Bool
                       , verbose :: Bool
                       , solver :: MR.Solver
                       , solverInteractionFile :: Maybe FilePath
                       , maximumModelCount :: Int
                       , threadCount :: Int
                       , timeoutSeconds :: Int
                       }
