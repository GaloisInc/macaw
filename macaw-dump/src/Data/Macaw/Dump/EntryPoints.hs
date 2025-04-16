{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.Dump.EntryPoints
  ( EntryPointsConfig(..)
  , entryPointsConfig
  , entryPoints
  ) where

import Data.ElfEdit qualified as EE
import Data.Foldable qualified as F
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.BinaryLoader qualified as Loader
import Data.Macaw.CFG qualified as MC
import Data.Macaw.Dump.CLIUtils qualified as MDCU
import Data.Macaw.Memory qualified as MM
import Data.Macaw.Memory.LoadCommon qualified as MML
import Data.Word (Word64)
import Options.Applicative qualified as Opt

data EntryPointsConfig = EntryPointsConfig
  { entryPointsLoadOffset :: Maybe Word64
  , entryPointsBinPath :: FilePath
  }

entryPointsConfig :: Opt.Parser EntryPointsConfig
entryPointsConfig =
  EntryPointsConfig
  <$> Opt.optional MDCU.loadOffsetOpt
  <*> MDCU.binOpt

loadOptions :: EntryPointsConfig -> MML.LoadOptions
loadOptions cfg = MML.LoadOptions { MML.loadOffset = entryPointsLoadOffset cfg }

entryPoints ::
  forall arch.
  ( MM.MemWidth (MC.ArchAddrWidth arch)
  , Loader.BinaryLoader arch (EE.ElfHeaderInfo (MC.ArchAddrWidth arch))
  ) =>
  MAI.ArchitectureInfo arch ->
  EntryPointsConfig ->
  IO ()
entryPoints archInfo cfg = do
  ehi <- MDCU.loadElf archInfo (entryPointsBinPath cfg)
  let loadOpts = loadOptions cfg
  loaded <- Loader.loadBinary @arch loadOpts ehi
  eps <- Loader.entryPoints loaded
  F.for_ eps print
