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
import qualified SemMC.ARM as ARMSem
import           SemMC.Architecture.ARM.Opcodes ( allA32Semantics, allA32OpcodeInfo )


execInstruction :: MC.Value ARMSem.ARM ids (MT.BVType 32)
                -> Dismantle.ARM.Instruction
                -> Maybe (Generator ARMSem.ARM ids s ())
execInstruction = $(genExecInstructionLogStdErr (Proxy @ARMSem.ARM)
                    (locToRegTH (Proxy @ARMSem.ARM))
                    armNonceAppEval
                    armAppEvaluator
                    'a32InstructionMatcher
                    allA32Semantics
                    allA32OpcodeInfo
                    ([t| Dismantle.ARM.Operand |], [t| ARMSem.ARM |])
                   )
