{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.Dump.Discover
  ( DiscoverException
  , DiscoverConfig(..)
  , discoverConfig
  , discover
  ) where

import Control.Exception qualified as X
import Control.Lens qualified as Lens
import Control.Monad qualified as Monad
import Data.ByteString qualified as BS
import Data.ElfEdit qualified as EE
import Data.Foldable qualified as F
import Data.Set qualified as Set
import Data.Macaw.Architecture.Info qualified as MAI
import Data.Macaw.CFG qualified as MC
import Data.Macaw.Dump.CLIUtils qualified as MDCU
import Data.Macaw.Discovery qualified as MD
import Data.Macaw.Memory.ElfLoader qualified as MEL
import Data.Macaw.Memory.LoadCommon qualified as MML
import Data.Macaw.Memory qualified as MM
import Data.Macaw.Symbolic qualified as MS
import Data.Map qualified as Map
import Data.Parameterized.Some (Some(Some))
import Data.Text.Encoding.Error qualified as Text
import Data.Text.Encoding qualified as Text
import Data.Text qualified as Text
import Lang.Crucible.Analysis.Postdom qualified as CAP
import Lang.Crucible.CFG.Core qualified as CCC
import Lang.Crucible.CFG.Extension qualified as CCE
import Lang.Crucible.FunctionHandle qualified as CFH
import Options.Applicative qualified as Opt
import Prettyprinter qualified as PP
import System.IO qualified as IO
import What4.FunctionName qualified as WF
import What4.ProgramLoc qualified as WPL

data DiscoverException = ELFResolutionError String
  deriving Show

instance X.Exception DiscoverException


-- | Convert machine addresses into What4 positions.
--
-- When possible, we map to the structured 'WPL.BinaryPos' type. However,
-- some 'MM.MemSegmentOff' values cannot be mapped to an absolute position
-- (e.g., some addresses from shared libraries are in non-trivial segments).
-- In those cases, we map to the unstructured 'WPL.Others' with a sufficiently
-- descriptive string.
posFn :: (MM.MemWidth w) => Text.Text -> MM.MemSegmentOff w -> WPL.Position
posFn binaryName segOff =
  case MM.segoffAsAbsoluteAddr segOff of
    Just mw -> WPL.BinaryPos binaryName (fromIntegral mw)
    Nothing -> WPL.OtherPos (binaryName <> Text.pack ": " <> Text.pack (show segOff))

-- | Load an ELF file into a macaw 'MM.Memory' (and symbols)
--
-- Prints warnings to stderr.
loadELF ::
  MML.LoadOptions ->
  EE.ElfHeaderInfo w ->
  IO (MM.Memory w, [MEL.MemSymbol w])
loadELF loadOpts ehi = do
  case MEL.resolveElfContents loadOpts ehi of
    Left err -> X.throwIO (ELFResolutionError err)
    Right (warnings, mem, _mentry, nameAddrList) -> do
      F.forM_ warnings $ \w -> do
        IO.hPutStrLn IO.stderr ("WARN: " ++ w)
      return (mem, nameAddrList)

-- | Run discovery on the provided symbols, or all if none are provided
runDiscovery ::
  forall arch w.
  ( MC.ArchAddrWidth arch ~ w
  , MC.ArchConstraints arch
  , MM.MemWidth w
  ) =>
  EE.ElfHeaderInfo w ->
  MAI.ArchitectureInfo arch ->
  Set.Set BS.ByteString ->
  IO (MD.DiscoveryState arch)
runDiscovery headerInfo archInfo symbols = do
  (mem, nameAddrList) <- loadELF MML.defaultLoadOptions headerInfo
  let addrSymMap =
        Map.fromList
          [ (MEL.memSymbolStart msym, name)
          | msym <- nameAddrList
          , let name = MEL.memSymbolName msym
          , Set.null symbols || Set.member name symbols
          ]
  pure (MD.cfgFromAddrs archInfo mem addrSymMap (Map.keys addrSymMap) [])

displayCfgs ::
  ( MC.ArchConstraints arch
  , MS.GenArchInfo MS.LLVMMemory arch
  , CCE.IsSyntaxExtension (MS.MacawExt arch)
  ) =>
  FilePath ->
  MD.DiscoveryState arch ->
  MS.GenArchVals mem arch ->
  -- | Also print Crucible CFG?
  Bool ->
  IO ()
displayCfgs path discState archVals printCrucible = do
  let funInfos = discState Lens.^. MD.funInfo
  halloc <- CFH.newHandleAllocator
  F.for_ (Map.toList funInfos) $ \(_addr, Some info) -> do
    Monad.when printCrucible $ do
      IO.putStrLn "== Macaw =="
    IO.print (PP.pretty info)
    Monad.when printCrucible $ do
      IO.putStrLn "\n== Crucible =="
      let pos = posFn (Text.pack path)
      let funName =
            WF.functionNameFromText $
              Text.decodeUtf8With Text.lenientDecode $
                MD.discoveredFunName info
      CCC.SomeCFG ssa <-
        MS.mkFunCFG (MS.archFunctions archVals) halloc funName pos info
      IO.print (CCC.ppCFG' True (CAP.postdomInfo ssa) ssa)

data DiscoverConfig = DiscoverConfig
  { -- Arguments
    discBinPath :: FilePath
  , discSymbols :: [BS.ByteString]
    -- Options
  , discPrintCrucible :: Bool
  }

discoverConfig :: Opt.Parser DiscoverConfig
discoverConfig =
  DiscoverConfig
  <$> MDCU.binOpt
  <*> Opt.many (Opt.strArgument (Opt.help "function name" <> Opt.metavar "SYMBOL"))
  <*> Opt.switch (Opt.long "crucible" <> Opt.help "output Crucible CFGs")

discover ::
  ( MC.ArchConstraints arch
  , MS.GenArchInfo MS.LLVMMemory arch
  , CCE.IsSyntaxExtension (MS.MacawExt arch)
  , MC.ArchConstraints arch
  , MM.MemWidth (MC.ArchAddrWidth arch)
  ) =>
  MAI.ArchitectureInfo arch ->
  MS.GenArchVals mem arch ->
  DiscoverConfig ->
  IO ()
discover archInfo archVals cfg = do
  ehi <- MDCU.loadElf archInfo (discBinPath cfg)
  let symbs = Set.fromList (discSymbols cfg)
  discState <- runDiscovery ehi archInfo symbs
  displayCfgs (discBinPath cfg) discState archVals (discPrintCrucible cfg)
