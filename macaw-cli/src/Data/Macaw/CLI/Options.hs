{-# LANGUAGE ApplicativeDo #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RecordWildCards #-}

module Data.Macaw.CLI.Options
  ( Opts(..)
  , getOpts
  ) where

import Control.Applicative ((<**>))
import Data.Text (Text)
import Options.Applicative qualified as Opt

data Opts = Opts
  { optsBinaryPath :: FilePath
  , optsEntrypoint :: Text
  } deriving Show

opts :: Opt.Parser Opts
opts = do
  optsBinaryPath <- Opt.strArgument (Opt.help "filename of binary" <> Opt.metavar "FILENAME" )
  optsEntrypoint <-
    Opt.strOption (Opt.long "entrypoint" <> Opt.help "name of entrypoint symbol" <> Opt.metavar "ENTRY")
  pure Opts{..}

optsInfo :: Opt.ParserInfo Opts
optsInfo =
  Opt.info
    (opts <**> Opt.helper)
    (  Opt.fullDesc
    <> Opt.header "Execute programs using macaw-symbolic"
    )

getOpts :: IO Opts
getOpts = Opt.execParser optsInfo
