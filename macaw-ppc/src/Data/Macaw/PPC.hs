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
  PPC64,
  PPC32,
  -- * ELF support
  tocBaseForELF,
  tocEntryAddrsForElf
  ) where

import           Data.Proxy ( Proxy(..) )

import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.Architecture.Info as MI
import           Data.Macaw.CFG
import qualified Data.Macaw.CFG.DemandSet as MDS
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types ( BVType )

import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

import Data.Macaw.PPC.Disassemble ( disassembleFn )
import Data.Macaw.PPC.Eval ( mkInitialAbsState,
                             absEvalArchFn,
                             absEvalArchStmt,
                             postCallAbsState,
                             postPPCTermStmtAbsState,
                             preserveRegAcrossSyscall
                           )
import Data.Macaw.PPC.Identify ( identifyCall,
                                 identifyReturn
                               )
import Data.Macaw.PPC.Arch ( rewriteTermStmt,
                             rewriteStmt,
                             rewritePrimFn,
                             ppcPrimFnHasSideEffects,
                             PPCArchConstraints
                           )
import Data.Macaw.PPC.BinaryFormat.ELF ( tocBaseForELF, tocEntryAddrsForElf )
import qualified Data.Macaw.PPC.Semantics.PPC32 as PPC32
import qualified Data.Macaw.PPC.Semantics.PPC64 as PPC64

-- | The type tag for 64 bit PowerPC
type PPC64 = PPC64.PPC

-- | The type tag for 32 bit PowerPC
type PPC32 = PPC32.PPC

archDemandContext :: (PPCArchConstraints ppc) => proxy ppc -> MDS.DemandContext ppc
archDemandContext _ =
  MDS.DemandContext { MDS.demandConstraints = \a -> a
                    , MDS.archFnHasSideEffects = ppcPrimFnHasSideEffects
                    }

-- | NOTE: There isn't necessarily one answer for this.  This will need to turn
-- into a function.  With PIC jump tables, it can be smaller than the native size.
jumpTableEntrySize :: (PPCArchConstraints ppc) => proxy ppc -> MM.MemWord (ArchAddrWidth ppc)
jumpTableEntrySize _ = 4

ppc64_linux_info :: (ArchSegmentOff PPC64.PPC -> Maybe (MA.AbsValue 64 (BVType 64))) -> MI.ArchitectureInfo PPC64.PPC
ppc64_linux_info tocMap =
  MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                      , MI.archAddrWidth = MM.Addr64
                      , MI.archEndianness = MM.BigEndian
                      , MI.jumpTableEntrySize = jumpTableEntrySize proxy
                      , MI.disassembleFn = disassembleFn proxy PPC64.execInstruction
                      , MI.mkInitialAbsState = mkInitialAbsState proxy tocMap
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.postCallAbsState = postCallAbsState proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewritePrimFn
                      , MI.rewriteArchStmt = rewriteStmt
                      , MI.rewriteArchTermStmt = rewriteTermStmt
                      , MI.archDemandContext = archDemandContext proxy
                      , MI.postArchTermStmtAbsState = postPPCTermStmtAbsState (preserveRegAcrossSyscall proxy)
                      }
  where
    proxy = Proxy @PPC64.PPC

ppc32_linux_info :: (ArchSegmentOff PPC32.PPC -> Maybe (MA.AbsValue 32 (BVType 32))) -> MI.ArchitectureInfo PPC32.PPC
ppc32_linux_info tocMap =
  MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                      , MI.archAddrWidth = MM.Addr32
                      , MI.archEndianness = MM.BigEndian
                      , MI.jumpTableEntrySize = jumpTableEntrySize proxy
                      , MI.disassembleFn = disassembleFn proxy PPC32.execInstruction
                      , MI.mkInitialAbsState = mkInitialAbsState proxy tocMap
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.postCallAbsState = postCallAbsState proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewritePrimFn
                      , MI.rewriteArchStmt = rewriteStmt
                      , MI.rewriteArchTermStmt = rewriteTermStmt
                      , MI.archDemandContext = archDemandContext proxy
                      , MI.postArchTermStmtAbsState = postPPCTermStmtAbsState (preserveRegAcrossSyscall proxy)
                      }
  where
    proxy = Proxy @PPC32.PPC

