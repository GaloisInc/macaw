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
import qualified Data.Macaw.ARM.Semantics.ARMSemantics as ARMSem
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.CFG.DemandSet as MDS
import qualified Data.Macaw.Memory as MM
import           Data.Proxy ( Proxy(..) )
import qualified SemMC.ARM as ARM


-- | The type tag for ARM (32-bit)
type ARM = ARM.ARM


arm_linux_info :: MI.ArchitectureInfo ARM.ARM
arm_linux_info =
    MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                        , MI.archAddrWidth = MM.Addr32
                        , MI.archEndianness = MM.LittleEndian
                        , MI.jumpTableEntrySize = 0 -- jumpTableEntrySize proxy
                        , MI.disassembleFn = disassembleFn proxy ARMSem.execInstruction
                        , MI.mkInitialAbsState = mkInitialAbsState proxy
                        , MI.absEvalArchFn = absEvalArchFn proxy
                        , MI.absEvalArchStmt = absEvalArchStmt proxy
                        , MI.postCallAbsState = error "TBD: postCallAbsState proxy"
                        , MI.identifyCall = error "TBD: identifyCall proxy"
                        , MI.identifyReturn = error "TBD: identifyReturn proxy"
                        , MI.rewriteArchFn = error "TBD: rewritePrimFn"
                        , MI.rewriteArchTermStmt = error "TBD: rewriteTermStmt"
                        , MI.rewriteArchStmt = rewriteStmt
                        , MI.archDemandContext = archDemandContext proxy
                        , MI.postArchTermStmtAbsState = postARMTermStmtAbsState (preserveRegAcrossSyscall proxy)
                        }
        where
          proxy = Proxy @ARM.ARM


archDemandContext :: (ARMArchConstraints arm) => proxy arm
                  -> MDS.DemandContext arm
archDemandContext _ =
  MDS.DemandContext { MDS.demandConstraints    = \a -> a
                    , MDS.archFnHasSideEffects = armPrimFnHasSideEffects
                    }
