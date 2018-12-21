{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.PPC (
  -- * Macaw configurations
  ppc32_linux_info,
  ppc64_linux_info,
  -- * Type-level tags
  AnyPPC,
  Variant,
  V64,
  V32,
  PPC64,
  PPC32,
  PPC.VariantRepr(..),
  PPC.KnownVariant(..),
  -- * PPC Types
  R.PPCReg(..),
  A.PPCTermStmt(..),
  A.PPCStmt(..),
  A.PPCPrimFn(..),
  ) where

import           Control.Lens ( (^.) )
import           Data.Maybe
import           Data.Proxy ( Proxy(..) )

import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.DemandSet as MDS
import qualified Data.Macaw.Memory as MM

import qualified SemMC.Architecture.PPC as PPC
import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

import qualified Data.Macaw.BinaryLoader as BL
import qualified Data.Macaw.BinaryLoader.PPC as BLP
import           Data.Macaw.PPC.Arch ( rewriteTermStmt
                                     , rewriteStmt
                                     , rewritePrimFn
                                     , ppcPrimFnHasSideEffects
                                     , PPCArchConstraints
                                     )
import qualified Data.Macaw.PPC.Arch as A
import           Data.Macaw.PPC.Disassemble ( disassembleFn, initialBlockRegs )
import           Data.Macaw.PPC.Eval ( mkInitialAbsState
                                     , absEvalArchFn
                                     , absEvalArchStmt
                                     , postCallAbsState
                                     , postPPCTermStmtAbsState
                                     , preserveRegAcrossSyscall
                                     )
import           Data.Macaw.PPC.Identify ( identifyCall
                                         , identifyReturn
                                         , matchReturn
                                         )
import qualified Data.Macaw.PPC.PPCReg as R
import qualified Data.Macaw.PPC.Semantics.PPC32 as PPC32
import qualified Data.Macaw.PPC.Semantics.PPC64 as PPC64

-- | The constructor for type tags for PowerPC
type AnyPPC = PPC.AnyPPC

-- | Data kind for specifying a PowerPC variant for 'AnyPPC'
type Variant = PPC.Variant

-- | The variant for 64-bit PowerPC
type V64 = PPC.V64

-- | The variant for 32-bit PowerPC
type V32 = PPC.V32

-- | The type tag for 64-bit PowerPC
type PPC64 = AnyPPC V64

-- | The type tag for 32-bit PowerPC
type PPC32 = AnyPPC V32

archDemandContext :: (PPCArchConstraints ppc) => proxy ppc -> MDS.DemandContext ppc
archDemandContext _ =
  MDS.DemandContext { MDS.demandConstraints = \a -> a
                    , MDS.archFnHasSideEffects = ppcPrimFnHasSideEffects
                    }
ppc64_linux_info :: ( BLP.HasTOC PPC64.PPC binFmt
                    ) =>
                    BL.LoadedBinary PPC64.PPC binFmt
                 -> MI.ArchitectureInfo PPC64.PPC
ppc64_linux_info binData =
  MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                      , MI.archAddrWidth = MM.Addr64
                      , MI.archEndianness = MM.BigEndian
                      , MI.mkInitialRegsForBlock = initialBlockRegs
                      , MI.disassembleFn = disassembleFn proxy PPC64.execInstruction
                      , MI.mkInitialAbsState = mkInitialAbsState proxy binData
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.postCallAbsState = postCallAbsState proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.checkForReturnAddr = \r s -> isJust $ matchReturn s (r ^. MC.boundValue R.PPC_LNK)
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewritePrimFn
                      , MI.rewriteArchStmt = rewriteStmt
                      , MI.rewriteArchTermStmt = rewriteTermStmt
                      , MI.archDemandContext = archDemandContext proxy
                      , MI.postArchTermStmtAbsState = postPPCTermStmtAbsState (preserveRegAcrossSyscall proxy)
                      }
  where
    proxy = Proxy @PPC64.PPC

ppc32_linux_info :: ( BLP.HasTOC PPC32.PPC binFmt
                    ) =>
                    BL.LoadedBinary PPC32.PPC binFmt
                 -> MI.ArchitectureInfo PPC32.PPC
ppc32_linux_info binData =
  MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                      , MI.archAddrWidth = MM.Addr32
                      , MI.archEndianness = MM.BigEndian
                      , MI.mkInitialRegsForBlock = initialBlockRegs
                      , MI.disassembleFn = disassembleFn proxy PPC32.execInstruction
                      , MI.mkInitialAbsState = mkInitialAbsState proxy binData
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.postCallAbsState = postCallAbsState proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.checkForReturnAddr = \r s -> isJust $ matchReturn s (r ^. MC.boundValue R.PPC_LNK)
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewritePrimFn
                      , MI.rewriteArchStmt = rewriteStmt
                      , MI.rewriteArchTermStmt = rewriteTermStmt
                      , MI.archDemandContext = archDemandContext proxy
                      , MI.postArchTermStmtAbsState = postPPCTermStmtAbsState (preserveRegAcrossSyscall proxy)
                      }
  where
    proxy = Proxy @PPC32.PPC

