{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Macaw.ARM
    ( -- * Macaw configurations
      arm_linux_info,
      -- * Type-level tags
      ARM,
      -- * ELF support
      -- tocBaseForELF
      -- tocEntryAddrsForELF
    )
    where

import           Data.Macaw.ARM.Arch
import           Data.Macaw.ARM.Disassemble ( disassembleFn )
import           Data.Macaw.ARM.Eval
import           Data.Macaw.ARM.Identify ( identifyCall, identifyReturn )
import qualified Data.Macaw.ARM.Semantics.ARMSemantics as ARMSem
import qualified Data.Macaw.ARM.Semantics.ThumbSemantics as ThumbSem
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.CFG.DemandSet as MDS
import qualified Data.Macaw.Memory as MM
import           Data.Proxy ( Proxy(..) )
import qualified SemMC.Architecture.AArch32 as ARM


-- | The type tag for ARM (32-bit).  Note that this includes both A32 and T32 modes.
type ARM = ARM.AArch32


arm_linux_info :: MI.ArchitectureInfo ARM.AArch32
arm_linux_info =
    MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                        , MI.archAddrWidth = MM.Addr32
                        , MI.archEndianness = MM.LittleEndian
                        , MI.disassembleFn = disassembleFn proxy ARMSem.execInstruction ThumbSem.execInstruction
                        , MI.mkInitialAbsState = mkInitialAbsState proxy
                        , MI.absEvalArchFn = absEvalArchFn proxy
                        , MI.absEvalArchStmt = absEvalArchStmt proxy
                        , MI.postCallAbsState = error "TBD: postCallAbsState proxy"
                        , MI.identifyCall = identifyCall proxy
                        , MI.identifyReturn = identifyReturn proxy
                        , MI.rewriteArchFn = rewritePrimFn
                        , MI.rewriteArchStmt = rewriteStmt
                        , MI.rewriteArchTermStmt = rewriteTermStmt
                        , MI.archDemandContext = archDemandContext proxy
                        , MI.postArchTermStmtAbsState = postARMTermStmtAbsState (preserveRegAcrossSyscall proxy)
                        }
        where
          proxy = Proxy @ARM.AArch32


archDemandContext :: (ARMArchConstraints arm) => proxy arm
                  -> MDS.DemandContext arm
archDemandContext _ =
  MDS.DemandContext { MDS.demandConstraints    = \a -> a
                    , MDS.archFnHasSideEffects = armPrimFnHasSideEffects
                    }
