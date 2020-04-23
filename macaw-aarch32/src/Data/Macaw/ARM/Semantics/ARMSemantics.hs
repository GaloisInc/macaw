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
import           Data.Macaw.ARM.ARMReg ( locToRegTH )
import           Data.Macaw.ARM.Arch ( a32InstructionMatcher )
import           Data.Macaw.ARM.Semantics.TH ( armAppEvaluator, armNonceAppEval, loadSemantics )
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.SemMC.TH ( genExecInstruction, genExecInstructionLogStdErr )
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..), mapSome )
import           Data.Proxy ( Proxy(..) )
import           Dismantle.ARM.A32 -- must be present to supply definitions for genExecInstruction output
import qualified Lang.Crucible.Backend.Simple as CBS
import qualified Language.Haskell.TH as TH
import qualified SemMC.Architecture.AArch32 as ARMSem
import           SemMC.Architecture.ARM.Opcodes ( ASLSemantics(..), allA32OpcodeInfo )
import qualified What4.Expr.Builder as WEB


execInstruction :: MC.Value ARMSem.AArch32 ids (MT.BVType 32)
                -> Instruction
                -> Maybe (Generator ARMSem.AArch32 ids s ())
execInstruction =
  $(do Some ng <- TH.runIO PN.newIONonceGenerator
       sym <- TH.runIO (CBS.newSimpleBackend CBS.FloatIEEERepr ng)
       sem <- TH.runIO (loadSemantics sym)
       let
         aconv :: (MapF.Pair (Opcode Operand) x)
               -> (MapF.Pair (ARMSem.ARMOpcode ARMSem.ARMOperand) x)
         aconv (MapF.Pair o b) = MapF.Pair (ARMSem.A32Opcode o) b
       genExecInstruction (Proxy @ARMSem.AArch32)
                    locToRegTH
                    armNonceAppEval
                    (armAppEvaluator MC.LittleEndian)
                    'a32InstructionMatcher
                    (MapF.fromList (fmap aconv (MapF.toList (a32Semantics sem)))) -- (fmap aconv (a32Semantics sem))
                    allA32OpcodeInfo
                    (funSemantics sem)
                    ([t| Operand |], [t| ARMSem.AArch32 |])
                    MC.LittleEndian
   )


