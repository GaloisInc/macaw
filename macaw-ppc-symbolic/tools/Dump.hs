{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.ByteString qualified as BS
import Data.ElfEdit qualified as EE
import Data.Macaw.BinaryLoader qualified as MBL
import Data.Macaw.Dump.CLI qualified as MDC
import Data.Macaw.Dump qualified as MD
import Data.Macaw.Memory.ElfLoader qualified as MM
import Data.Macaw.PPC qualified as PPC
import Data.Macaw.PPC.Symbolic ()
import Data.Macaw.Symbolic qualified as MS
import Data.Proxy (Proxy(..))
import Data.Set qualified as Set
import System.Exit qualified as Exit
import System.IO qualified as IO

die :: String -> IO a
die msg = do
  IO.hPutStrLn IO.stderr msg
  Exit.exitFailure

main :: IO ()
main = do
  cli <- MDC.parseCli
  let exePath = MDC.cliBinPath cli
  bytes <- BS.readFile exePath
  case EE.decodeElfHeaderInfo bytes of
    Left (_, msg) -> die ("Error parsing ELF header from file '" ++ exePath ++ "': " ++ msg)
    Right (EE.SomeElf ehi) -> do
      let symbs = Set.fromList (MDC.cliSymbols cli)
      case EE.headerClass (EE.header ehi) of
        EE.ELFCLASS32 -> do
          discState <- MD.runDiscovery ehi PPC.ppc32_linux_info symbs
          archVals <-
            case MS.archVals (Proxy @PPC.PPC32) Nothing of
              Just archVals -> pure archVals
              Nothing -> error "impossible"
          MD.displayCfgs exePath discState archVals (MDC.cliPrintCrucible cli)
        EE.ELFCLASS64 -> do
          loadedBinary <- MBL.loadBinary MM.defaultLoadOptions ehi
          let archInfo = PPC.ppc64_linux_info loadedBinary
          discState <- MD.runDiscovery ehi archInfo symbs
          archVals <-
            case MS.archVals (Proxy @PPC.PPC64) Nothing of
              Just archVals -> pure archVals
              Nothing -> error "impossible"
          MD.displayCfgs exePath discState archVals (MDC.cliPrintCrucible cli)
