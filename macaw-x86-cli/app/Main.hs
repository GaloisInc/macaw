{-# LANGUAGE ImportQualifiedPost #-}

module Main where

import Data.Text.IO qualified as Text

-- First-party
import Data.Macaw.CLI qualified as MCLI
import Data.Macaw.CLI.Options qualified as MCO
import Data.Macaw.X86.CLI qualified as MX86CLI

main :: IO ()
main = do
  mres <- MX86CLI.simFile =<< MCO.getOpts
  case mres of
    Nothing -> MX86CLI.bail "Entrypoint not found!"
    Just res -> Text.putStrLn (MCLI.ppSimRes res)
 
