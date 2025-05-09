{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
module Initialization (
  withElf
  , withRefinedDiscovery
  ) where

import           GHC.TypeNats

import           Control.Monad.IO.Class ( MonadIO, liftIO )
import qualified Control.Monad.Catch as X
import qualified Control.Monad.Reader as MR
import qualified Control.Monad.IO.Unlift as MU
import qualified Data.ByteString as BS
import qualified Data.ElfEdit as EE
import qualified Data.Map as M
import           Data.Proxy ( Proxy(..) )
import qualified Lang.Crucible.LLVM.MemModel as LLVM
import qualified Lumberjack as LJ
import qualified Prettyprinter as PP
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
        -> (forall arch binFmt . (16 <= MC.ArchAddrWidth arch, SymArchConstraints arch, MBL.BinaryLoader arch binFmt) => Proxy arch -> AI.ArchitectureInfo arch -> MBL.LoadedBinary arch binFmt -> MD.DiscoveryState arch -> IO a)
        -> IO a
withElf opts k = do
  bs <- BS.readFile (inputFile opts)
  case EE.decodeElfHeaderInfo bs of
    Right (EE.SomeElf elf) -> do
      let hdr = EE.header elf
      case (EE.headerClass hdr, EE.headerMachine hdr) of
        (EE.ELFCLASS64, EE.EM_PPC64) -> do
          bin <- MBL.loadBinary @PPC64.PPC ML.defaultLoadOptions elf
          let archInfo = MP.ppc64_linux_info bin
          withLoadedBinary k archInfo bin
        (EE.ELFCLASS64, EE.EM_X86_64) -> do
          bin <- MBL.loadBinary @MX86.X86_64 ML.defaultLoadOptions elf
          withLoadedBinary k MX86.x86_64_linux_info bin
        (EE.ELFCLASS32, EE.EM_PPC) -> do
          bin <- MBL.loadBinary @PPC32.PPC ML.defaultLoadOptions elf
          let archInfo = MP.ppc32_linux_info
          withLoadedBinary k archInfo bin
        (_,m) -> X.throwM (UnsupportedArchitecture m)
    Left (_, s) -> do
      IO.hPutStrLn IO.stderr ("Error loading ELF binary:\n  " ++ s)
      IOE.exitFailure

withLoadedBinary :: forall arch binFmt m a
                  . ( MBL.BinaryLoader arch binFmt
                    , X.MonadThrow m
                    )
                 => (Proxy arch -> AI.ArchitectureInfo arch -> MBL.LoadedBinary arch binFmt -> MD.DiscoveryState arch -> m a)
                 -> AI.ArchitectureInfo arch
                 -> MBL.LoadedBinary arch binFmt
                 -> m a
withLoadedBinary k archInfo bin = do
  entries <- MBL.entryPoints bin
  let dstate0 = MD.cfgFromAddrs archInfo (MBL.memoryImage bin) M.empty entries []
  k (Proxy @arch) archInfo bin dstate0

newtype Refine arch a = Refine { runRefine_ :: MR.ReaderT (Env arch) IO a }
  deriving ( Functor
           , Monad
           , Applicative
           , MU.MonadUnliftIO
           , MonadIO
           , X.MonadThrow
           , MR.MonadReader (Env arch)
           )

data Env arch = Env { logger :: LJ.LogAction (Refine arch) (MR.RefinementLog arch) }

instance LJ.HasLog (MR.RefinementLog arch) (Refine arch) where
  getLogAction = MR.asks logger

runRefine :: (ML.MemWidth (MC.ArchAddrWidth arch)) => Refine arch a -> IO a
runRefine a = MR.runReaderT (runRefine_ a) env0
  where
    doLog msg = liftIO $ IO.hPutStrLn IO.stderr (show (PP.pretty msg))
    env0 = Env (LJ.LogAction doLog)


-- | Run the SMT-based refinement on a binary
withRefinedDiscovery :: forall arch binFmt a
                      . ( 16 <= MC.ArchAddrWidth arch
                        , SymArchConstraints arch
                        , MBL.BinaryLoader arch binFmt
                        , ML.MemWidth (MC.ArchAddrWidth arch)
                        , ?memOpts :: LLVM.MemOptions
                        )
                     => Options
                     -> AI.ArchitectureInfo arch
                     -> MBL.LoadedBinary arch binFmt
                     -> (MD.DiscoveryState arch -> MR.RefinementInfo arch -> IO a)
                     -> IO a
withRefinedDiscovery opts archInfo bin k = do
  AI.withArchConstraints archInfo $ do
    let config = MR.defaultRefinementConfig { MR.solver = solver opts
                                            , MR.solverInteractionFile = solverInteractionFile opts
                                            , MR.maximumModelCount = maximumModelCount opts
                                            , MR.parallelismFactor = max 1 (threadCount opts)
                                            , MR.timeoutSeconds = max 1 (timeoutSeconds opts)
                                            }
    ctx <- MR.defaultRefinementContext config bin
    entries <- MBL.entryPoints bin
    (dstate, info) <- runRefine @arch $ MR.cfgFromAddrsWith ctx archInfo (MBL.memoryImage bin) M.empty entries []
    k dstate info
