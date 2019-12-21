{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Initialization (
  withElf
  , withRefinedDiscovery
  ) where

import           GHC.TypeNats

import qualified Control.Monad.Catch as X
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as EE
import qualified Data.Foldable as F
import qualified Data.Map as M
import qualified System.IO as IO
import qualified System.Exit as IOE

import qualified Data.Macaw.Architecture.Info as AI
import qualified Data.Macaw.BinaryLoader as MBL
import           Data.Macaw.BinaryLoader.X86 ()
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory.ElfLoader as ML
import           Data.Macaw.Symbolic ( SymArchConstraints )
import qualified Data.Macaw.PPC as MP
import           Data.Macaw.PPC.Symbolic ()
import qualified Data.Macaw.X86 as MX86
import           Data.Macaw.X86.Symbolic ()
import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

import qualified Data.Macaw.Refinement as MR
import           Options ( Options(..) )

data InitError = UnsupportedArchitecture EE.ElfMachine
  deriving (Show)

instance X.Exception InitError

-- | Load an ELF file from disk and run code discovery on it
--
-- The continuation has access to all of the intermediate results of the process
withElf :: Options
        -> (forall arch binFmt . (16 <= MC.ArchAddrWidth arch, SymArchConstraints arch, MBL.BinaryLoader arch binFmt) => AI.ArchitectureInfo arch -> MBL.LoadedBinary arch binFmt -> MD.DiscoveryState arch -> IO a)
        -> IO a
withElf opts k = do
  bs <- BS.readFile (inputFile opts)
  case EE.parseElf bs of
    EE.Elf64Res warnings elf -> mapM_ (IO.hPutStrLn IO.stderr . show) warnings >> withElf64 elf
    EE.Elf32Res warnings elf -> mapM_ (IO.hPutStrLn IO.stderr . show) warnings >> withElf32 elf
    EE.ElfHeaderError _ s -> do
      IO.hPutStrLn IO.stderr ("Error loading ELF binary:\n  " ++ s)
      IOE.exitFailure
  where
    withElf64 elf =
      case EE.elfMachine elf of
        EE.EM_PPC64 -> do
          bin <- MBL.loadBinary @PPC64.PPC ML.defaultLoadOptions elf
          let archInfo = MP.ppc64_linux_info bin
          withLoadedBinary k archInfo bin
        EE.EM_X86_64 -> do
          bin <- MBL.loadBinary @MX86.X86_64 ML.defaultLoadOptions elf
          withLoadedBinary k MX86.x86_64_linux_info bin
        m -> X.throwM (UnsupportedArchitecture m)

    withElf32 elf =
      case EE.elfMachine elf of
        EE.EM_PPC -> do
          bin <- MBL.loadBinary @PPC32.PPC ML.defaultLoadOptions elf
          let archInfo = MP.ppc32_linux_info bin
          withLoadedBinary k archInfo bin
        m -> X.throwM (UnsupportedArchitecture m)

withLoadedBinary :: ( MBL.BinaryLoader arch binFmt
                    , X.MonadThrow m
                    )
                 => (AI.ArchitectureInfo arch -> MBL.LoadedBinary arch binFmt -> MD.DiscoveryState arch -> m a)
                 -> AI.ArchitectureInfo arch
                 -> MBL.LoadedBinary arch binFmt
                 -> m a
withLoadedBinary k archInfo bin = do
  entries <- F.toList <$> MBL.entryPoints bin
  let dstate0 = MD.cfgFromAddrs archInfo (MBL.memoryImage bin) M.empty entries []
  k archInfo bin dstate0

-- | Run the SMT-based refinement on a binary
withRefinedDiscovery :: ( 16 <= MC.ArchAddrWidth arch
                        , SymArchConstraints arch
                        , MBL.BinaryLoader arch binFmt
                        )
                     => Options
                     -> AI.ArchitectureInfo arch
                     -> MBL.LoadedBinary arch binFmt
                     -> (MD.DiscoveryState arch -> IO a)
                     -> IO a
withRefinedDiscovery opts archInfo bin k = do
  AI.withArchConstraints archInfo $ do
    let config = MR.defaultRefinementConfig { MR.solver = solver opts
                                            , MR.solverInteractionFile = solverInteractionFile opts
                                            , MR.maximumModelCount = maximumModelCount opts
                                            , MR.parallelismFactor = min 1 (threadCount opts)
                                            }
    ctx <- MR.defaultRefinementContext config bin
    entries <- F.toList <$> MBL.entryPoints bin
    dstate <- MR.cfgFromAddrs ctx archInfo (MBL.memoryImage bin) M.empty entries []
    k dstate
