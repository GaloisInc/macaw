{-# OPTIONS_GHC -w -ddump-splices -ddump-to-file -dth-dec-file #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Data.Macaw.ARM.Semantics.ARMSemantics
    ( execInstruction
    )
    where

import qualified Data.ByteString as BS
import qualified Data.List as L
import           Data.Macaw.ARM.ARMReg ( locToRegTH )
import           Data.Macaw.ARM.Arch ( a32InstructionMatcher )
import           Data.Macaw.ARM.Semantics.TH ( armAppEvaluator, armNonceAppEval, loadSemantics )
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.SemMC.TH ( MacawTHConfig(..), genExecInstruction )
import qualified Data.Macaw.Types as MT
import           Data.Parameterized.Classes ( showF )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..), mapSome )
import           Data.Proxy ( Proxy(..) )
import           Dismantle.ARM.A32 -- must be present to supply definitions for genExecInstruction output
import qualified Lang.Crucible.Backend.Simple as CBS
import qualified Language.Haskell.TH as TH
import qualified SemMC.Architecture.AArch32 as ARMSem
import           SemMC.Architecture.ARM.Opcodes ( ASLSemantics(..), allA32OpcodeInfo )
import qualified SemMC.Formula as SF
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

       let notVecOpc :: forall tps . ARMSem.ARMOpcode ARMSem.ARMOperand tps -> Bool
           notVecOpc opc = not ("V" `L.isPrefixOf` showF opc)
       let notVecLib :: forall sym . Some (SF.FunctionFormula sym) -> Bool
           notVecLib (Some lf) =
             case lf of
               SF.FunctionFormula { SF.ffName = nm } ->
                 not ("df_V" `L.isInfixOf` nm)
       let thConf = MacawTHConfig { locationTranslator = locToRegTH
                                  , nonceAppTranslator = armNonceAppEval
                                  , appTranslator = armAppEvaluator MC.LittleEndian
                                  , instructionMatchHook = 'a32InstructionMatcher
                                  , archEndianness = MC.LittleEndian
                                  , operandTypeQ = [t| Operand |]
                                  , archTypeQ = [t| ARMSem.AArch32 |]
                                  , genLibraryFunction = notVecLib
                                  , genOpcodeCase = notVecOpc
                                  }

       genExecInstruction (Proxy @ARMSem.AArch32)
                          thConf
                          (MapF.fromList (fmap aconv (MapF.toList (a32Semantics sem))))
                          allA32OpcodeInfo
                          (funSemantics sem)
   )


