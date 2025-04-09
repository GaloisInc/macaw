{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}

module Data.Macaw.ARM
    ( -- * Macaw configurations
      arm_linux_info,
      armPLTStubInfo,
      -- * Type-level tags
      ARM,
    )
    where

import           Control.Applicative ( (<|>) )
import qualified Data.ElfEdit as EE
import           Data.Macaw.ARM.Arch
import           Data.Macaw.ARM.Disassemble ( disassembleFn )
import           Data.Macaw.ARM.Eval
import           Data.Macaw.ARM.Identify ( identifyCall, identifyReturn, isReturnValue, conditionalReturnClassifier, conditionalCallClassifier )
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import qualified Data.Macaw.ARM.Semantics.ARMSemantics as ARMSem
import qualified Data.Macaw.ARM.Semantics.ThumbSemantics as ThumbSem
import qualified Data.Macaw.CFG as MC
import           Control.Lens ( (^.) )
import qualified Data.Macaw.Architecture.Info as MI
import qualified Data.Macaw.CFG.DemandSet as MDS
import qualified Data.Macaw.Discovery as MD
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader.PLTStubs as MMEP
import qualified SemMC.Architecture.AArch32 as ARM


-- | The type tag for ARM (32-bit).  Note that this includes both A32 and T32 modes.
type ARM = ARM.AArch32


arm_linux_info :: MI.ArchitectureInfo ARM.AArch32
arm_linux_info =
    MI.ArchitectureInfo { MI.withArchConstraints = \x -> x
                        , MI.archAddrWidth = MM.Addr32
                        , MI.archEndianness = MM.LittleEndian
                        , MI.extractBlockPrecond = extractBlockPrecond
                        , MI.initialBlockRegs = initialBlockRegs
                        , MI.disassembleFn = disassembleFn ARMSem.execInstruction ThumbSem.execInstruction
                        , MI.mkInitialAbsState = mkInitialAbsState
                        , MI.absEvalArchFn = absEvalArchFn
                        , MI.absEvalArchStmt = absEvalArchStmt
                        , MI.identifyCall = identifyCall
                        , MI.archCallParams = callParams preserveRegAcrossSyscall
                        , MI.checkForReturnAddr = \r s -> isReturnValue s (r ^. MC.boundValue ARMReg.lr)
                        , MI.identifyReturn = identifyReturn
                        , MI.rewriteArchFn = rewritePrimFn
                        , MI.rewriteArchStmt = rewriteStmt
                        , MI.rewriteArchTermStmt = rewriteTermStmt
                        , MI.archDemandContext = archDemandContext
                        , MI.postArchTermStmtAbsState = postARMTermStmtAbsState preserveRegAcrossSyscall
                        , MI.archClassifier = conditionalCallClassifier <|> conditionalReturnClassifier <|> MD.defaultClassifier
                        }

archDemandContext :: MDS.DemandContext ARM.AArch32
archDemandContext =
  MDS.DemandContext { MDS.demandConstraints    = \a -> a
                    , MDS.archFnHasSideEffects = armPrimFnHasSideEffects
                    }

-- | PLT stub information for ARM32 relocation types.
armPLTStubInfo :: MMEP.PLTStubInfo EE.ARM32_RelocationType
armPLTStubInfo = MMEP.PLTStubInfo
  { MMEP.pltFunSize     = 20
  , MMEP.pltStubSize    = 12
  , MMEP.pltGotStubSize = error "Unexpected .plt.got section in ARM32 binary"
  }
