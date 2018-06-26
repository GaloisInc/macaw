{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-spec-constr -fno-specialise -fmax-simplifier-iterations=1 -fno-call-arity #-}

module Data.Macaw.ARM.Semantics.ARMSemantics
    ( execInstruction
    )
    where

import           Data.Macaw.ARM.ARMReg ( locToRegTH )
import           Data.Macaw.ARM.Arch ( a32InstructionMatcher )
import           Data.Macaw.ARM.Operand
import           Data.Macaw.ARM.Semantics.TH ( armAppEvaluator, armNonceAppEval )
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.SemMC.TH ( genExecInstructionLogStdErr )
import qualified Data.Macaw.Types as MT
import           Data.Proxy ( Proxy(..) )
import           Dismantle.ARM -- must be present to supply definitions for genExecInstruction output
import qualified SemMC.Architecture.AArch32 as ARMSem
import           SemMC.Architecture.ARM.Opcodes ( allA32Semantics, allA32OpcodeInfo, a32DefinedFunctions )


execInstruction :: MC.Value ARMSem.AArch32 ids (MT.BVType 32)
                -> Dismantle.ARM.Instruction
                -> Maybe (Generator ARMSem.AArch32 ids s ())
execInstruction = $(genExecInstructionLogStdErr (Proxy @ARMSem.AArch32)
                    (locToRegTH (Proxy @ARMSem.AArch32))
                    armNonceAppEval
                    armAppEvaluator
                    'a32InstructionMatcher
                    allA32Semantics
                    allA32OpcodeInfo
                    a32DefinedFunctions
                    ([t| Dismantle.ARM.Operand |], [t| ARMSem.AArch32 |])
                   )
