{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.CLI
  ( sim
  ) where

import Control.Lens qualified as Lens
import Control.Monad qualified as Monad
import Data.ByteString.Char8 qualified as BS8
import Data.Map qualified as Map 
import Data.Text (Text)
import Data.Text qualified as Text 
import GHC.TypeLits (KnownNat)

-- First-party
import Data.ElfEdit qualified as Elf
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.CFG qualified as MCFG
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
  FilePath ->
  Elf.ElfHeaderInfo (MD.ArchAddrWidth arch) ->
  Text ->
  IO ()
sim archInfo archVals pltStubInfo extractor binPath elfHeaderInfo entryFn = do
  Some.Some nonceGen <- PN.newIONonceGenerator
  binfo <- MST.runDiscovery elfHeaderInfo binPath MST.toAddrSymMap archInfo pltStubInfo
  let discState = MST.binaryDiscState (MST.mainBinaryInfo binfo)
  let funInfos = Map.elems (discState Lens.^. MD.funInfo)
  let entryFn8 = BS8.pack (Text.unpack entryFn)
  Monad.forM_ funInfos $ \(Some.Some dfi) -> do
    case MD.discoveredFunSymbol dfi of
      Just funSymb | entryFn8 `BS8.isPrefixOf` funSymb -> do
        let floatMode = WEB.FloatRealRepr -- TODO: make configurable via cli
        sym <- WEB.newExprBuilder floatMode MacawCLI nonceGen
        -- TODO: make solver configurable via cli
        CBO.withYicesOnlineBackend sym CBO.NoUnsatFeatures WPF.noFeatures $ \bak -> do
          let solver = WSY.yicesAdapter
          execFeatures <- MST.defaultExecFeatures (MST.SomeOnlineBackend bak)
          let ?memOpts = LLVM.defaultMemOptions
          let mmPreset = MST.DefaultMemModel -- TODO: make configurable via cli
          simRes <- MST.simulateAndVerify solver WS.defaultLogData bak execFeatures archInfo archVals binfo mmPreset extractor dfi
          case simRes of
            MST.SimulationAborted -> putStrLn "Aborted!"
            MST.SimulationTimeout -> putStrLn "Timeout!"
            MST.SimulationPartial -> putStrLn "Partial!"  -- TODO: ???
            MST.SimulationResult MST.Unsat -> putStrLn "Always returns 0"
            MST.SimulationResult MST.Sat -> putStrLn "May return non-zero"
            MST.SimulationResult MST.Unknown -> putStrLn "Solver returned unknown!"
      _ -> pure ()
