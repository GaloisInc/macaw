{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}

module Main where

import Data.ByteString qualified as BS
import Data.List qualified as List 
import Data.Proxy qualified as Proxy
import Data.Text (Text)
import Data.Text qualified as Text 
import System.Exit qualified as Exit 

-- First-party
import Data.ElfEdit qualified as Elf
import Data.Macaw.CLI qualified as MCLI
import Data.Macaw.Symbolic qualified as MS
import Data.Macaw.Symbolic.Testing qualified as MST
import Data.Macaw.X86 qualified as X86
import Data.Macaw.X86.Symbolic ()
import Data.Parameterized.Classes qualified as PC
import Lang.Crucible.Backend qualified as CB
import Lang.Crucible.Simulator.RegMap qualified as CSRM

bail :: String -> IO a
bail msg = do
  putStrLn msg
  Exit.exitFailure

x86ResultExtractor ::
  CB.IsSymInterface sym =>
  MS.ArchVals X86.X86_64 ->
  MST.ResultExtractor sym X86.X86_64
x86ResultExtractor archVals = MST.ResultExtractor $ \regs _sp _mem k -> do
  let re = MS.lookupReg archVals regs X86.RAX
  k PC.knownRepr (CSRM.regValue re)

simX86_64 ::
  FilePath ->
  Elf.ElfHeaderInfo 64 ->
  Text ->
  IO ()
simX86_64 binPath elfHeaderInfo entryFn = do
  archVals <- case MS.archVals (Proxy.Proxy @X86.X86_64) Nothing of
                Just archVals -> pure archVals
                Nothing -> bail "Internal error: no archVals?"
  MCLI.sim X86.x86_64_linux_info archVals X86.x86_64PLTStubInfo (x86ResultExtractor archVals) binPath elfHeaderInfo entryFn
 
simFile ::
  FilePath ->
  Text ->
  IO ()
simFile binPath entryFn = do
  bs <- BS.readFile binPath
  case Elf.decodeElfHeaderInfo bs of
    Right (Elf.SomeElf hdr) ->
      case (Elf.headerClass (Elf.header hdr), Elf.headerMachine (Elf.header hdr)) of
        (Elf.ELFCLASS64, Elf.EM_X86_64) -> simX86_64 binPath hdr entryFn
        (_, mach) -> bail ("User error: unexpected ELF architecture: " List.++ show mach)
    Left _ ->
      bail ("User error: expected x86_64 ELF binary, but found non-ELF file at " List.++ binPath)

-- TODO: CLI
main :: IO ()
main = simFile "test.exe" (Text.pack "entry")
 
