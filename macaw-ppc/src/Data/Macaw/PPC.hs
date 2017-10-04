{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}

module Data.Macaw.PPC (
  ppc32_linux_info,
  ppc64_linux_info
  ) where

import           Data.Proxy ( Proxy(..) )

import qualified Data.Macaw.Architecture.Info as MI
import Data.Macaw.CFG
import qualified Data.Macaw.CFG.DemandSet as MDS
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Parameterized.Some ( Some(..), viewSome )

import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

import Data.Macaw.PPC.Disassemble ( disassembleFn )
import Data.Macaw.PPC.Eval ( mkInitialAbsState,
                             absEvalArchFn,
                             absEvalArchStmt,
                             postCallAbsState,
                             preserveRegAcrossSyscall
                           )
import Data.Macaw.PPC.Identify ( identifyCall,
                                 identifyReturn
                               )
import Data.Macaw.PPC.Arch ( rewriteTermStmt,
                             rewriteStmt,
                             rewritePrimFn,
                             valuesInPPCStmt,
                             ppcPrimFnHasSideEffects,
                             PPCArch
                           )
import Data.Macaw.PPC.PPCReg ( PPCWidth )
import qualified Data.Macaw.PPC.Semantics.PPC32 as PPC32
import qualified Data.Macaw.PPC.Semantics.PPC64 as PPC64

addValueListDemands :: [Some (Value ppc ids)] -> MDS.DemandComp ppc ids ()
addValueListDemands = mapM_ (viewSome MDS.addValueDemands)

archDemandContext :: (PPCArch ppc) => proxy ppc -> MDS.DemandContext ppc ids
archDemandContext _ =
  MDS.DemandContext { MDS.addArchStmtDemands = addValueListDemands . valuesInPPCStmt
                    , MDS.addArchFnDemands = addValueListDemands . FC.foldMapFC (\v -> [ Some v ])
                    , MDS.archFnHasSideEffects = ppcPrimFnHasSideEffects
                    }

-- | NOTE: There isn't necessarily one answer for this.  This will need to turn
-- into a function.  With PIC jump tables, it can be smaller than the native size.
jumpTableEntrySize :: (PPCWidth ppc) => proxy ppc -> MM.MemWord (ArchAddrWidth ppc)
jumpTableEntrySize _ = 4

ppc64_linux_info :: MI.ArchitectureInfo PPC64.PPC
ppc64_linux_info =
  MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                      , MI.archAddrWidth = MM.Addr64
                      , MI.archEndianness = MM.BigEndian
                      , MI.jumpTableEntrySize = jumpTableEntrySize proxy
                      , MI.disassembleFn = disassembleFn proxy PPC64.execInstruction
                      , MI.preserveRegAcrossSyscall = preserveRegAcrossSyscall proxy
                      , MI.mkInitialAbsState = mkInitialAbsState proxy
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.postCallAbsState = postCallAbsState proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewritePrimFn
                      , MI.rewriteArchStmt = rewriteStmt
                      , MI.rewriteArchTermStmt = rewriteTermStmt
                      , MI.archDemandContext = archDemandContext proxy
                      }
  where
    proxy = Proxy @PPC64.PPC

ppc32_linux_info :: MI.ArchitectureInfo PPC32.PPC
ppc32_linux_info =
  MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                      , MI.archAddrWidth = MM.Addr32
                      , MI.archEndianness = MM.BigEndian
                      , MI.jumpTableEntrySize = jumpTableEntrySize proxy
                      , MI.disassembleFn = disassembleFn proxy PPC32.execInstruction
                      , MI.preserveRegAcrossSyscall = preserveRegAcrossSyscall proxy
                      , MI.mkInitialAbsState = mkInitialAbsState proxy
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.postCallAbsState = postCallAbsState proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewritePrimFn
                      , MI.rewriteArchStmt = rewriteStmt
                      , MI.rewriteArchTermStmt = rewriteTermStmt
                      , MI.archDemandContext = archDemandContext proxy
                      }
  where
    proxy = Proxy @PPC32.PPC

