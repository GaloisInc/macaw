{-# OPTIONS_GHC -w -ddump-splices -ddump-to-file -dth-dec-file #-}

{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Data.Macaw.ARM.Semantics.ARMSemantics
    ( execInstruction
    )
    where


import qualified Data.ByteString as BS
import qualified Language.Haskell.TH as TH
import           Data.Macaw.ARM.ARMReg ( locToRegTH )
import           Data.Macaw.ARM.Arch ( a32InstructionMatcher )
import           Data.Macaw.ARM.Semantics.TH ( armAppEvaluator, armNonceAppEval, loadSemantics )
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.SemMC.TH ( genExecInstruction, genExecInstructionLogStdErr )
import qualified Data.Macaw.Types as MT
import           Data.Proxy ( Proxy(..) )
import           Dismantle.ARM.A32 -- must be present to supply definitions for genExecInstruction output
import qualified SemMC.Architecture.AArch32 as ARMSem
import           SemMC.Architecture.ARM.Opcodes ( ASLSemantics(..), allA32OpcodeInfo )
import           Data.Parameterized.Some

execInstruction :: MC.Value ARMSem.AArch32 ids (MT.BVType 32)
                -> Instruction
                -> Maybe (Generator ARMSem.AArch32 ids s ())
execInstruction =
  $(do sem <- TH.runIO loadSemantics    
       let
         aconv :: (Some (Opcode Operand), BS.ByteString) -> (Some (ARMSem.ARMOpcode ARMSem.ARMOperand), BS.ByteString)
         aconv (o,b) = (mapSome ARMSem.A32Opcode o, b)
       genExecInstructionLogStdErr (Proxy @ARMSem.AArch32)
                    (locToRegTH (Proxy @ARMSem.AArch32))
                    armNonceAppEval
                    (armAppEvaluator MC.LittleEndian)
                    'a32InstructionMatcher
                    (fmap aconv (a32Semantics sem))
                    allA32OpcodeInfo
                    (funSemantics sem)
                    ([t| Operand |], [t| ARMSem.AArch32 |])
                    MC.LittleEndian
   )

