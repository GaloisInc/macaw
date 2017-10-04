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
import qualified Data.Macaw.Types as MT

import qualified Dismantle.PPC as D
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
import Data.Macaw.PPC.PPCReg
import Data.Macaw.PPC.Rewrite ( rewriteArchFn,
                                rewriteArchStmt,
                                rewriteArchTermStmt
                              )
import Data.Macaw.PPC.Generator ( PPCGenerator )

archDemandContext :: proxy ppc -> MDS.DemandContext ppc ids
archDemandContext = undefined

-- | NOTE: There isn't necessarily one answer for this.  This will need to turn
-- into a function.  With PIC jump tables, it can be smaller than the native size.
jumpTableEntrySize :: proxy ppc -> MM.MemWord (ArchAddrWidth ppc)
jumpTableEntrySize = undefined

ppc64_linux_info :: MI.ArchitectureInfo PPC64.PPC
ppc64_linux_info =
  MI.ArchitectureInfo { MI.withArchConstraints = undefined
                      , MI.archAddrWidth = undefined
                      , MI.archEndianness = MM.BigEndian
                      , MI.jumpTableEntrySize = jumpTableEntrySize proxy
                      , MI.disassembleFn = disassembleFn proxy lookupSemantics
                      , MI.preserveRegAcrossSyscall = preserveRegAcrossSyscall proxy
                      , MI.mkInitialAbsState = mkInitialAbsState proxy
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.postCallAbsState = postCallAbsState proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewriteArchFn proxy
                      , MI.rewriteArchStmt = rewriteArchStmt proxy
                      , MI.rewriteArchTermStmt = rewriteArchTermStmt proxy
                      , MI.archDemandContext = archDemandContext proxy
                      }
  where
    proxy = Proxy @PPC64.PPC
    lookupSemantics = undefined

ppc32_linux_info :: MI.ArchitectureInfo PPC32.PPC
ppc32_linux_info =
  MI.ArchitectureInfo { MI.withArchConstraints = undefined
                      , MI.archAddrWidth = undefined
                      , MI.archEndianness = MM.BigEndian
                      , MI.jumpTableEntrySize = jumpTableEntrySize proxy
                      , MI.disassembleFn = disassembleFn proxy lookupSemantics
                      , MI.preserveRegAcrossSyscall = preserveRegAcrossSyscall proxy
                      , MI.mkInitialAbsState = mkInitialAbsState proxy
                      , MI.absEvalArchFn = absEvalArchFn proxy
                      , MI.absEvalArchStmt = absEvalArchStmt proxy
                      , MI.postCallAbsState = postCallAbsState proxy
                      , MI.identifyCall = identifyCall proxy
                      , MI.identifyReturn = identifyReturn proxy
                      , MI.rewriteArchFn = rewriteArchFn proxy
                      , MI.rewriteArchStmt = rewriteArchStmt proxy
                      , MI.rewriteArchTermStmt = rewriteArchTermStmt proxy
                      , MI.archDemandContext = archDemandContext proxy
                      }
  where
    proxy = Proxy @PPC32.PPC
    lookupSemantics = undefined

