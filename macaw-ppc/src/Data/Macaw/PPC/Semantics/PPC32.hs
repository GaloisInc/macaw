{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Data.Macaw.PPC.Semantics.PPC32
  ( execInstruction
  ) where

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import           Dismantle.PPC
import qualified Lang.Crucible.Backend.Simple as CBS
import qualified Language.Haskell.TH as TH
import qualified SemMC.Architecture.PPC as SP
import           SemMC.Architecture.PPC32.Opcodes ( allSemantics, allOpcodeInfo, allDefinedFunctions )
import qualified SemMC.Formula as SF
import qualified SemMC.Util as SU

import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.SemMC.TH ( MacawTHConfig(..), genExecInstruction )
import           Data.Macaw.PPC.Arch ( ppcInstructionMatcher )
import           Data.Macaw.PPC.PPCReg ( locToRegTH )
import           Data.Macaw.PPC.Semantics.TH ( ppcAppEvaluator, ppcNonceAppEval )

execInstruction :: MC.Value (SP.AnyPPC SP.V32) ids (MT.BVType 32) -> Instruction -> Maybe (Generator (SP.AnyPPC SP.V32) ids s ())
execInstruction =
  $(do let proxy = Proxy @(SP.AnyPPC SP.V32)
       Some ng <- TH.runIO PN.newIONonceGenerator
       sym <- TH.runIO (CBS.newSimpleBackend CBS.FloatIEEERepr ng)

       logCfg <- TH.runIO SU.mkNonLogCfg
       let ?logCfg = logCfg

       env <- TH.runIO (SF.formulaEnv proxy sym)
       lib <- TH.runIO (SF.loadLibrary proxy sym env allDefinedFunctions)
       formulas <- TH.runIO (SF.loadFormulas sym env lib allSemantics)

       let genOpc :: forall tps . Opcode Operand tps -> Bool
           genOpc _ = True
       let thConf = MacawTHConfig { locationTranslator = locToRegTH (Proxy @SP.V32)
                                  , nonceAppTranslator = ppcNonceAppEval
                                  , appTranslator = ppcAppEvaluator
                                  , instructionMatchHook = 'ppcInstructionMatcher
                                  , archEndianness = MM.BigEndian
                                  , operandTypeQ = [t| Dismantle.PPC.Operand |]
                                  , archTypeQ = [t| (SP.AnyPPC SP.V32) |]
                                  , genLibraryFunction = \_ -> True
                                  , genOpcodeCase = genOpc
                                  , archTranslateType = \_ _ _ -> Nothing
                                  }

       genExecInstruction proxy
                          thConf
                          formulas
                          allOpcodeInfo
                          lib
   )
