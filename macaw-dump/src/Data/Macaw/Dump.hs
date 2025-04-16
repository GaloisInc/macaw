{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE MonoLocalBinds #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Dump
  ( main
  ) where

import Data.ElfEdit qualified as EE
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.Dump.CLI qualified as MDC
import Data.Macaw.Dump.Discover qualified as MDD
import Data.Macaw.Dump.EntryPoints qualified as MDE
import Data.Macaw.Dump.Memory qualified as MDM
import Data.Macaw.Dump.Plt qualified as MDP
import Data.Macaw.CFG qualified as MC
import Data.Macaw.Memory.ElfLoader.PLTStubs qualified as MMEP
import Data.Macaw.Symbolic qualified as MS
import Lang.Crucible.CFG.Extension qualified as CCE
import Data.Macaw.BinaryLoader qualified as Loader

main ::
  ( MS.GenArchInfo MS.LLVMMemory arch
  , CCE.IsSyntaxExtension (MS.MacawExt arch)
  , MC.ArchConstraints arch
  , MC.ArchAddrWidth arch ~ EE.RelocationWidth reloc
  , EE.IsRelocationType reloc
  , Loader.BinaryLoader arch (EE.ElfHeaderInfo (MC.ArchAddrWidth arch))
  ) =>
  MAI.ArchitectureInfo arch ->
  MS.GenArchVals mem arch ->
  MMEP.PLTStubInfo reloc ->
  IO ()
main archInfo archVals pltStubInfo = do
  cli <- MDC.parseCli
  case MDC.cliCommand cli of
    MDC.CommandDiscover cfg -> MDD.discover archInfo archVals cfg
    MDC.CommandEntryPoints cfg -> MDE.entryPoints archInfo cfg
    MDC.CommandMemory cfg -> MDM.memory archInfo cfg
    MDC.CommandPlt cfg -> MDP.plt archInfo pltStubInfo cfg
