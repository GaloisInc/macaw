{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}

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


import           Data.Macaw.ARM.Disassemble ( disassembleFn )
import           Data.Macaw.ARM.Eval
import qualified Data.Macaw.ARM.Semantics.ARMSemantics as ARMSem
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.Memory as MM
import           Data.Proxy ( Proxy(..) )
import qualified SemMC.ARM as ARM


-- | The type tag for ARM (32-bit)
type ARM = ARM.ARM


arm_linux_info :: MI.ArchitectureInfo ARM.ARM
arm_linux_info =
    MI.ArchitectureInfo { MI.withArchConstraints = undefined -- \x -> x
                        , MI.archAddrWidth = MM.Addr32
                        , MI.archEndianness = MM.LittleEndian
                        , MI.jumpTableEntrySize = 0 -- undefined -- jumpTableEntrySize proxy
                        , MI.disassembleFn = disassembleFn proxy ARMSem.execInstruction
                        , MI.mkInitialAbsState = mkInitialAbsState proxy
                        , MI.absEvalArchFn = undefined -- absEvalArchFn proxy
                        , MI.absEvalArchStmt = undefined -- absEvalArchStmt proxy
                        , MI.postCallAbsState = undefined -- postCallAbsState proxy
                        , MI.identifyCall = undefined -- identifyCall proxy
                        , MI.identifyReturn = undefined -- identifyReturn proxy
                        , MI.rewriteArchFn = undefined -- rewritePrimFn
                        , MI.rewriteArchStmt = undefined -- rewriteStmt
                        , MI.rewriteArchTermStmt = undefined -- rewriteTermStmt
                        , MI.archDemandContext = undefined -- archDemandContext proxy
                        , MI.postArchTermStmtAbsState = undefined -- postARMTermStmtAbsState (preserveRegAcrossSyscall proxy)
                        }
        where
          proxy = Proxy @ARM.ARM
