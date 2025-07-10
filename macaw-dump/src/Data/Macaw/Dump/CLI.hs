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
import Data.Macaw.Dump.EntryPoints qualified as MDE
import Data.Macaw.Dump.Memory qualified as MDM
import Data.Macaw.Dump.Plt qualified as MDP
import Options.Applicative qualified as Opt

data Command
  = CommandDiscover MDD.DiscoverConfig
  | CommandEntryPoints MDE.EntryPointsConfig
  | CommandMemory MDM.MemoryConfig
  | CommandPlt MDP.PltConfig

command :: Opt.Parser Command
command =
  Opt.subparser $
    mconcat
    [ cmdDiscover
    , cmdEntryPoints
    , cmdMemory
    , cmdPlt
    ]
  where
  cmdDiscover :: Opt.Mod Opt.CommandFields Command
  cmdDiscover = do
    Opt.command
      "discover"
      (Opt.info (CommandDiscover <$> MDD.discoverConfig) (Opt.progDesc "Perform code discovery and print CFGs"))

  cmdEntryPoints :: Opt.Mod Opt.CommandFields Command
  cmdEntryPoints = do
    Opt.command
      "entry-points"
      (Opt.info (CommandEntryPoints <$> MDE.entryPointsConfig) (Opt.progDesc "Print entry points"))

  cmdMemory :: Opt.Mod Opt.CommandFields Command
  cmdMemory = do
    Opt.command
      "memory"
      (Opt.info (CommandMemory <$> MDM.memoryConfig) (Opt.progDesc "Print program memory"))

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
  helperInfo
    cli
    (  Opt.fullDesc
    <> Opt.header
         "A tool to display internal Macaw data structures"
    )

parseCli :: IO Cli
parseCli = Opt.execParser cliInfo

-- | Helper, not exported
--
-- Create a 'Opt.ParserInfo' with a @--help@ option.
helperInfo :: Opt.Parser a -> Opt.InfoMod a -> Opt.ParserInfo a
helperInfo parser = Opt.info (parser <**> Opt.helper)
