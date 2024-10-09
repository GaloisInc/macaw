{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RecordWildCards #-}

module Data.Macaw.Dump.CLI
  ( Cli(..)
  , parseCli
  ) where

import Control.Applicative ((<**>))
import Data.ByteString (ByteString)
import Options.Applicative qualified as Opt

data Cli = Cli
  { -- Arguments
    cliBinPath :: FilePath
  , cliSymbols :: [ByteString]
    -- Options
  , cliPrintCrucible :: Bool
  } deriving Show

opts :: Opt.Parser Cli
opts = do
  cliBinPath <- Opt.strArgument (Opt.help "filename of binary" <> Opt.metavar "FILENAME" )
  cliSymbols <- Opt.many $ Opt.strArgument (Opt.help "function name" <> Opt.metavar "SYMBOL")
  cliPrintCrucible <- Opt.switch (Opt.long "crucible" <> Opt.help "output Crucible CFGs")
  pure Cli{..}

cliInfo :: Opt.ParserInfo Cli
cliInfo =
  Opt.info
    (opts <**> Opt.helper)
    (  Opt.fullDesc
    <> Opt.header
         "A tool to display internal Macaw data structures"
    )

parseCli :: IO Cli
parseCli = Opt.execParser cliInfo
