{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}

module Data.Macaw.Dump.Memory
  ( MemoryConfig(..)
  , memoryConfig
  , memory
  ) where

import Data.ElfEdit qualified as EE
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.BinaryLoader qualified as Loader
import Data.Macaw.CFG.Core qualified as MC
import Data.Macaw.Dump.CLIUtils qualified as MDCU
import Data.Macaw.Memory.LoadCommon qualified as LC
import Data.Macaw.Memory qualified as MM
import Data.Word (Word64)
import Options.Applicative qualified as Opt

data MemoryConfig
  = MemoryConfig
    { memLoadOffset :: Maybe Word64
    , memBinPath :: FilePath
    }

loadOffsetOpt :: Opt.Parser Word64
loadOffsetOpt = Opt.option Opt.auto opts
  where
  opts =
    mconcat
    [ Opt.long "offset"
    , Opt.help "base offset at which to load the file"
    , Opt.showDefault
    ]

memoryConfig :: Opt.Parser MemoryConfig
memoryConfig =
  MemoryConfig
  <$> Opt.optional loadOffsetOpt
  <*> MDCU.binOpt

loadOptions :: MemoryConfig -> LC.LoadOptions
loadOptions cfg = LC.LoadOptions { LC.loadOffset = memLoadOffset cfg }

memory ::
  forall arch.
  ( MM.MemWidth (MC.ArchAddrWidth arch)
  , Loader.BinaryLoader arch (EE.ElfHeaderInfo (MC.ArchAddrWidth arch))
  ) =>
  MAI.ArchitectureInfo arch ->
  MemoryConfig ->
  IO ()
memory archInfo cfg = do
  ehi <- MDCU.loadElf archInfo (memBinPath cfg)
  let loadOpts = loadOptions cfg
  loaded <- Loader.loadBinary @arch loadOpts ehi
  let mem = Loader.memoryImage loaded
  print mem
