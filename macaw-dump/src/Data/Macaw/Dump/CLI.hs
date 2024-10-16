{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RecordWildCards #-}

module Data.Macaw.Dump.CLI
  ( Cli(..)
  , Command(..)
  , parseCli
  ) where

import Control.Applicative ((<**>))
import Data.Macaw.Dump.Discover qualified as MDD
import Data.Macaw.Dump.Plt qualified as MDP
import Options.Applicative qualified as Opt

data Command
  = CommandDiscover MDD.DiscoverConfig
  | CommandPlt MDP.PltConfig

command :: Opt.Parser Command
command =
  Opt.subparser $
    mconcat
    [ cmdDiscover
    , cmdPlt
    ]
  where
  cmdDiscover :: Opt.Mod Opt.CommandFields Command
  cmdDiscover = do
    Opt.command
      "discover"
      (Opt.info (CommandDiscover <$> MDD.discoverConfig) (Opt.progDesc "Perform code discovery and print CFGs"))

  cmdPlt :: Opt.Mod Opt.CommandFields Command
  cmdPlt = do
    Opt.command
      "plt"
      (Opt.info (CommandPlt <$> MDP.pltConfig) (Opt.progDesc "Display PLT stubs"))

data Cli = Cli
  { cliCommand :: Command
  }

cli :: Opt.Parser Cli
cli = do
  cliCommand <- command
  pure Cli{..}

cliInfo :: Opt.ParserInfo Cli
cliInfo =
  Opt.info
    (cli <**> Opt.helper)
    (  Opt.fullDesc
    <> Opt.header
         "A tool to display internal Macaw data structures"
    )

parseCli :: IO Cli
parseCli = Opt.execParser cliInfo
