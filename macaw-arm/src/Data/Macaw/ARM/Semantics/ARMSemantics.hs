{-# LANGUAGE DataKinds #-}

module Data.Macaw.ARM.Semantics.ARMSemantics
    ( execInstruction
    )
    where

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import           SemMC.ARM ( ARM, Instruction )
import           Data.Macaw.SemMC.Generator ( Generator )
-- import           SemMC.Architecture.ARM.Opcodes ( allSemantics, allOpcodeInfo )

execInstruction :: MC.Value ARM ids (MT.BVType 32) -> Instruction -> Maybe (Generator ARM ids s ())
execInstruction = undefined
-- execInstruction = $(genExecInstruction (Proxy @ARM) (locToRegTH (Proxy @ARM)) armNonceAppEval armAppEvaluator 'armInstructionMatcher allSemantics allOpcodeInfo)
