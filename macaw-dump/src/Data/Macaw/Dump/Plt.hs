{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Dump.Plt
  ( PltConfig(..)
  , pltConfig
  , plt
  ) where

import Data.ElfEdit qualified as EE
import Data.Foldable qualified as F
import Data.Map qualified as Map
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.CFG qualified as MC
import Data.Macaw.Dump.CLIUtils qualified as MDCU
import Data.Macaw.Memory.ElfLoader.PLTStubs as MMEP
import Data.Macaw.Memory.LoadCommon qualified as MML
import Data.Macaw.Memory qualified as MM
import Options.Applicative qualified as Opt
import Prettyprinter as PP
import System.IO qualified as IO

data PltConfig = PltConfig
  { pltBinPath :: FilePath
  }

pltConfig :: Opt.Parser PltConfig
pltConfig =
  PltConfig
  <$> MDCU.binOpt

plt ::
  ( MC.ArchAddrWidth arch ~ EE.RelocationWidth reloc
  , MM.MemWidth (MC.ArchAddrWidth arch)
  , EE.IsRelocationType reloc
  ) =>
  MAI.ArchitectureInfo arch ->
  MMEP.PLTStubInfo reloc ->
  PltConfig ->
  IO ()
plt archInfo pltStubInfo cfg = do
  ehi <- MDCU.loadElf archInfo (pltBinPath cfg)
  let pltStubMap = MMEP.pltStubSymbols pltStubInfo MML.defaultLoadOptions ehi
  F.for_ (Map.toAscList pltStubMap) $ \(addr, (symtabEntry, _)) -> do
    IO.print (PP.pretty addr PP.<> PP.pretty ":" PP.<+> PP.viaShow (EE.steName symtabEntry))
