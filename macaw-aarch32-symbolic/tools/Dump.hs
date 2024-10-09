{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.ByteString qualified as BS
import Data.ElfEdit qualified as EE
import Data.Macaw.AArch32.Symbolic ()
import Data.Macaw.ARM qualified as MA
import Data.Macaw.Dump qualified as MD
import Data.Macaw.Dump.CLI qualified as MDC
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
      case EE.headerClass (EE.header ehi) of
        EE.ELFCLASS32 -> do
          let symbs = Set.fromList (MDC.cliSymbols cli)
          discState <- MD.runDiscovery ehi MA.arm_linux_info symbs
          archVals <-
            case MS.archVals (Proxy @MA.ARM) Nothing of
              Just archVals -> pure archVals
              Nothing -> error "impossible"
          MD.displayCfgs exePath discState archVals (MDC.cliPrintCrucible cli)
        EE.ELFCLASS64 -> die "Only 32-bit ARM is supported"
