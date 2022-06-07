{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Shared (
  withPPCELF
  ) where

import qualified Data.ByteString as B

import qualified Data.ElfEdit as E

import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.BinaryLoader as MBL
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory.ElfLoader as MM

import qualified Data.Macaw.PPC as RO
import           Data.Macaw.PPC.PPCReg ()
import qualified Data.Macaw.BinaryLoader.PPC ()

withPPCELF :: FilePath -> (forall arch w . (Show (MC.ArchBlockPrecond arch), MC.ArchAddrWidth arch ~ w, MBL.BinaryLoader arch (E.ElfHeaderInfo w), MM.MemWidth w, MC.ArchConstraints arch) => MAI.ArchitectureInfo arch -> MBL.LoadedBinary arch (E.ElfHeaderInfo w) -> IO ()) -> IO ()
withPPCELF fp k = do
  bytes <- B.readFile fp
  case E.decodeElfHeaderInfo bytes of
    Left (off,err) ->
      error ("Error parsing ELF header at offset " ++ show off ++ ": " ++ err
            )
    Right (E.SomeElf e) ->
      case (E.headerClass (E.header e), E.headerMachine (E.header e)) of
        (E.ELFCLASS64, E.EM_PPC64) -> do
          loadedBinary <- MBL.loadBinary loadCfg e
          let archInfo = RO.ppc64_linux_info loadedBinary
          k archInfo loadedBinary
        (E.ELFCLASS32, E.EM_PPC) -> do
          loadedBinary <- MBL.loadBinary loadCfg e
          let archInfo = RO.ppc32_linux_info
          k archInfo loadedBinary
        (klass, machine) -> error ("Unexpected ELF machine: " ++ show machine ++ " at ELFCLASS " ++ show klass)

loadCfg :: MM.LoadOptions
loadCfg = MM.defaultLoadOptions
          { MM.loadOffset = Just 0
          }
