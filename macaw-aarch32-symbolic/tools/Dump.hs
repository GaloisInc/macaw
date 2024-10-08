{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main (main) where

import Data.ByteString qualified as BS
import Data.ElfEdit qualified as EE
import Data.Macaw.AArch32.Symbolic ()
import Data.Macaw.ARM qualified as MA
import Data.Macaw.Dump qualified as Dump
import Data.Macaw.Symbolic qualified as MS
import Data.Proxy (Proxy(..))
import Data.Set qualified as Set
import System.Environment qualified as Env

go :: FilePath -> IO ()
go exePath = do
  bytes <- BS.readFile exePath
  case EE.decodeElfHeaderInfo bytes of
    Left (_, msg) -> error ("Error parsing ELF header from file '" ++ show exePath ++ "': " ++ msg)
    Right (EE.SomeElf ehi) -> do
      case EE.headerClass (EE.header ehi) of
        EE.ELFCLASS32 -> do
          discState <- Dump.runDiscovery ehi MA.arm_linux_info Set.empty
          archVals <-
            case MS.archVals (Proxy @MA.ARM) Nothing of
              Just archVals -> pure archVals
              Nothing -> error "impossible"
          Dump.displayCfgs exePath discState archVals False
        EE.ELFCLASS64 -> error "Only 32-bit ARM is supported"

main :: IO ()
main = do
  args <- Env.getArgs
  case args of
    [exePath] -> go exePath
    _ -> error "Bad arguments"
