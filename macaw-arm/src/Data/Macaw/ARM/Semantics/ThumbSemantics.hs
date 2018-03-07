{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-spec-constr -fno-specialise -fmax-simplifier-iterations=1 -fno-call-arity #-}

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
import qualified SemMC.ARM as ARMSem
import           SemMC.Architecture.ARM.Opcodes ( allT32Semantics, allT32OpcodeInfo )


execInstruction :: MC.Value ARMSem.ARM ids (MT.BVType 32)
                -> Dismantle.Thumb.Instruction
                -> Maybe (Generator ARMSem.ARM ids s ())
execInstruction = $(genExecInstructionLogStdErr (Proxy @ARMSem.ARM)
                    (locToRegTH (Proxy @ARMSem.ARM))
                    armNonceAppEval
                    armAppEvaluator
                    't32InstructionMatcher
                    allT32Semantics
                    allT32OpcodeInfo
                    ([t| Dismantle.Thumb.Operand |], [t| ARMSem.ARM |])
                   )
