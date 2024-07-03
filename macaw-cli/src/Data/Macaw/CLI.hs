{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.CLI
  ( sim
  , ppSimRes
  ) where

import Control.Lens qualified as Lens
import Data.ByteString.Char8 qualified as BS8
import Data.List qualified as List
import Data.Map qualified as Map 
import Data.Text qualified as Text 
import GHC.TypeLits (KnownNat)

-- First-party
import Data.ElfEdit qualified as Elf
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.CFG qualified as MCFG
import Data.Macaw.CLI.Options qualified as MCO
import Data.Macaw.Discovery qualified as MD
import Data.Macaw.Memory.ElfLoader.PLTStubs qualified as MPLT
import Data.Macaw.Symbolic qualified as MS
import Data.Macaw.Symbolic.Testing qualified as MST
import Data.Parameterized.NatRepr qualified as PNat
import Data.Parameterized.Nonce qualified as PN
import Data.Parameterized.Some qualified as Some
import Lang.Crucible.Backend qualified as CB
import Lang.Crucible.Backend.Online qualified as CBO
import Lang.Crucible.CFG.Extension qualified as CCE
import Lang.Crucible.LLVM.MemModel qualified as LLVM
import What4.Expr.Builder qualified as WEB
import What4.ProblemFeatures qualified as WPF
import What4.Solver qualified as WS
import What4.Solver.Yices qualified as WSY

data MacawCLI t = MacawCLI

-- | Simulate a function using 'MST.simulateAndVerify'
sim ::
  (1 PNat.<= MCFG.ArchAddrWidth arch) =>
  (16 PNat.<= MCFG.ArchAddrWidth arch) =>
  MCFG.MemWidth (MCFG.ArchAddrWidth arch) =>
  CCE.IsSyntaxExtension (MS.MacawExt arch) =>
  KnownNat (MCFG.ArchAddrWidth arch) =>
  (Elf.RelocationWidth reloc ~ MCFG.ArchAddrWidth arch) =>
  Elf.IsRelocationType reloc =>
  MAI.ArchitectureInfo arch ->
  MS.GenArchVals MS.LLVMMemory arch ->
  MPLT.PLTStubInfo reloc ->
  (forall sym. CB.IsSymInterface sym => MST.ResultExtractor sym arch) ->
  Elf.ElfHeaderInfo (MD.ArchAddrWidth arch) ->
  MCO.Opts ->
  -- | 'Nothing' when the entrypoint couldn\'t be found
  IO (Maybe MST.SimulationResult)
sim archInfo archVals pltStubInfo extractor elfHeaderInfo opts = do
  let binPath = MCO.optsBinaryPath opts
  let entryFn = MCO.optsEntrypoint opts
  Some.Some nonceGen <- PN.newIONonceGenerator
  binfo <- MST.runDiscovery elfHeaderInfo binPath MST.toAddrSymMap archInfo pltStubInfo
  let discState = MST.binaryDiscState (MST.mainBinaryInfo binfo)
  let funInfos = Map.elems (discState Lens.^. MD.funInfo)
  let entryFn8 = BS8.pack (Text.unpack entryFn)
  let isEntry sdfi = 
        case sdfi of
          Some.Some dfi ->
            case MD.discoveredFunSymbol dfi of
              Just funSymb -> entryFn8 `BS8.isPrefixOf` funSymb
              Nothing -> False
  let mEntry = List.find isEntry funInfos
  case mEntry of
    Nothing -> pure Nothing
    Just (Some.Some dfi) -> do
      let floatMode = WEB.FloatRealRepr -- TODO: make configurable via cli
      sym <- WEB.newExprBuilder floatMode MacawCLI nonceGen
      -- TODO: make solver configurable via cli
      CBO.withYicesOnlineBackend sym CBO.NoUnsatFeatures WPF.noFeatures $ \bak -> do
        let solver = WSY.yicesAdapter
        execFeatures <- MST.defaultExecFeatures (MST.SomeOnlineBackend bak)
        let ?memOpts = LLVM.defaultMemOptions
        let mmPreset = MST.DefaultMemModel -- TODO: make configurable via cli
        Just <$> MST.simulateAndVerify solver WS.defaultLogData bak execFeatures archInfo archVals binfo mmPreset extractor dfi

ppSimRes :: MST.SimulationResult -> Text.Text
ppSimRes =
  \case
    MST.SimulationAborted -> "Aborted!"
    MST.SimulationTimeout -> "Timeout!"
    MST.SimulationPartial -> "Partial!"  -- TODO: What does this mean?
    MST.SimulationResult MST.Unsat -> "Always returns 0"
    MST.SimulationResult MST.Sat -> "May return non-zero"
    MST.SimulationResult MST.Unknown -> "Solver returned unknown!"
