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
  ppcReadPCClassifier,
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
import           Control.Applicative ( (<|>) )

import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.DemandSet as MDS
import qualified Data.Macaw.Discovery as MD
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
import           Data.Macaw.PPC.Disassemble ( disassembleFn )
import qualified Data.Macaw.PPC.Eval as PPC.Eval
import           Data.Macaw.PPC.Eval ( mkInitialAbsState
                                     , absEvalArchFn
                                     , absEvalArchStmt
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
import qualified Control.Monad.Reader as CMR

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

archDemandContext :: (PPCArchConstraints var) => proxy var -> MDS.DemandContext (PPC.AnyPPC var)
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
                      , MI.disassembleFn = disassembleFn proxy PPC64.execInstruction
                      , MI.mkInitialAbsState = mkInitialAbsState proxy (Just toc)
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.checkForReturnAddr = \r s -> isJust $ matchReturn s (r ^. MC.boundValue R.PPC_LNK)
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewritePrimFn
                      , MI.rewriteArchStmt = rewriteStmt
                      , MI.rewriteArchTermStmt = rewriteTermStmt
                      , MI.archDemandContext = archDemandContext proxy
                      , MI.postArchTermStmtAbsState = postPPCTermStmtAbsState (preserveRegAcrossSyscall proxy)
                      , MI.initialBlockRegs = PPC.Eval.ppcInitialBlockRegs
                      , MI.archCallParams = PPC.Eval.ppcCallParams (preserveRegAcrossSyscall proxy)
                      , MI.extractBlockPrecond = PPC.Eval.ppcExtractBlockPrecond
                      , MI.archClassifier = ppcReadPCClassifier <|> MD.defaultClassifier
                      }
  where
    proxy = Proxy @PPC.V64
    toc = BLP.getTOC binData

ppc32_linux_info :: MI.ArchitectureInfo PPC32.PPC
ppc32_linux_info =
  MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                      , MI.archAddrWidth = MM.Addr32
                      , MI.archEndianness = MM.BigEndian
                      , MI.disassembleFn = disassembleFn proxy PPC32.execInstruction
                      , MI.mkInitialAbsState = mkInitialAbsState proxy Nothing
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.checkForReturnAddr = \r s -> isJust $ matchReturn s (r ^. MC.boundValue R.PPC_LNK)
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewritePrimFn
                      , MI.rewriteArchStmt = rewriteStmt
                      , MI.rewriteArchTermStmt = rewriteTermStmt
                      , MI.archDemandContext = archDemandContext proxy
                      , MI.postArchTermStmtAbsState = postPPCTermStmtAbsState (preserveRegAcrossSyscall proxy)
                      , MI.initialBlockRegs = PPC.Eval.ppcInitialBlockRegs
                      , MI.archCallParams = PPC.Eval.ppcCallParams (preserveRegAcrossSyscall proxy)
                      , MI.extractBlockPrecond = PPC.Eval.ppcExtractBlockPrecond
                      , MI.archClassifier = ppcReadPCClassifier <|> MD.defaultClassifier
                      }
  where
    proxy = Proxy @PPC.V32


-- | This classifier handles a ppc-specific pattern used to read the pc
--   in order to do pc-relative loads for relocatable code.
--
--   To do this, the pc is loaded into the link register by "calling" a
--   function at the immediate next address, causing the LR and
--   the pc to be equal. The original LR value 
--   is then restored before the function return.
--
--  e.g.
--  0x000018f8      mflr    r0
--  0x000018fc      bdnzl   0x1900
--  0x00001900      mflr    r30
--  0x00001904      lwz     r9, -0x20(r30)
--  ...
--  0x00001bd4      mtlr    r0
--  0x00001bd8      blr
--
--  This stashes the original LR in r0, and then the pc (i.e. 0x1900) in the
--  LR, which is then used to do a pc-relative load into r9.
--  Before the function returns, the original LR is restored from r0.

ppcReadPCClassifier :: PPCArchConstraints v => MD.BlockClassifier (AnyPPC v) ids
ppcReadPCClassifier = MI.classifierName "PPCReadPC" $ do
  bcc <- CMR.ask
  let ctx = MI.classifierParseContext bcc
  let finalRegs = MI.classifierFinalRegState bcc
  let ainfo = MI.pctxArchInfo ctx
  let mem = MI.pctxMemory ctx
  ret <- case MI.identifyCall ainfo mem (MI.classifierStmts bcc) finalRegs of
           Just (_prev_stmts, ret) -> pure ret
           Nothing -> fail "no call identified"
  let targets = MD.identifyCallTargets mem (MI.classifierAbsState bcc) finalRegs
  case targets of
    [target] | target == ret -> MD.directJumpClassifier
    _ -> fail $ ("call is not a pc read: " ++ show targets)