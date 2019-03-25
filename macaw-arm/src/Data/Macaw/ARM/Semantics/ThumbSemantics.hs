{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Data.Macaw.ARM.Semantics.ThumbSemantics
    ( execInstruction
    )
    where

import           Data.Macaw.ARM.ARMReg ( locToRegTH )
import           Data.Macaw.ARM.Arch ( t32InstructionMatcher )
import           Data.Macaw.ARM.Operand ()
import           Data.Macaw.ARM.Semantics.TH ( armAppEvaluator, armNonceAppEval )
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.SemMC.TH ( genExecInstructionLogStdErr )
import qualified Data.Macaw.Types as MT
import           Data.Proxy ( Proxy(..) )
import           Dismantle.Thumb -- as ThumbDis -- must be present to supply definitions for genExecInstruction output
import qualified SemMC.Architecture.AArch32 as ARMSem
import           SemMC.Architecture.ARM.Opcodes ( allT32Semantics, allT32OpcodeInfo, t32DefinedFunctions )


execInstruction :: MC.Value ARMSem.AArch32 ids (MT.BVType 32)
                -> Dismantle.Thumb.Instruction
                -> Maybe (Generator ARMSem.AArch32 ids s ())
execInstruction = $(genExecInstructionLogStdErr (Proxy @ARMSem.AArch32)
                    (locToRegTH (Proxy @ARMSem.AArch32))
                    armNonceAppEval
                    armAppEvaluator
                    't32InstructionMatcher
                    allT32Semantics
                    allT32OpcodeInfo
                    t32DefinedFunctions
                    ([t| Dismantle.Thumb.Operand |], [t| ARMSem.AArch32 |])
                   )
