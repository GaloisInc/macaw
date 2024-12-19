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
import Options.Applicative qualified as Opt

data MemoryConfig
  = MemoryConfig
    { memBinPath :: FilePath
    }

memoryConfig :: Opt.Parser MemoryConfig
memoryConfig =
  MemoryConfig
  <$> MDCU.binOpt

-- Currently, we do not apply any offsets to addresses in the loaded binary. We
-- will need to reconsider this if we want to support shared libraries.
loadOptions :: LC.LoadOptions
loadOptions =
  LC.LoadOptions
    { LC.loadOffset = Nothing
    }

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
  loaded <- Loader.loadBinary @arch loadOptions ehi
  let mem = Loader.memoryImage loaded
  print mem
