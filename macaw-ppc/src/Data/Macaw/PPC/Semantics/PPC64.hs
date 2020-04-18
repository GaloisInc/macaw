{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Data.Macaw.PPC.Semantics.PPC64
  ( execInstruction
  ) where

import           Data.Proxy ( Proxy(..) )
import           Dismantle.PPC
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT
import qualified SemMC.Architecture.PPC as SP
import           SemMC.Architecture.PPC64.Opcodes ( allSemantics, allOpcodeInfo
                                                  , allDefinedFunctions )

import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.SemMC.TH ( genExecInstruction )
import           Data.Macaw.PPC.Arch ( ppcInstructionMatcher )
import           Data.Macaw.PPC.PPCReg ( locToRegTH )
import           Data.Macaw.PPC.Semantics.TH ( ppcAppEvaluator, ppcNonceAppEval )

execInstruction :: MC.Value (SP.AnyPPC SP.V64) ids (MT.BVType 64) -> Instruction -> Maybe (Generator (SP.AnyPPC SP.V64) ids s ())
execInstruction = $(genExecInstruction (Proxy @(SP.AnyPPC SP.V64)) (locToRegTH (Proxy @SP.V64)) ppcNonceAppEval ppcAppEvaluator 'ppcInstructionMatcher allSemantics allOpcodeInfo allDefinedFunctions
                    ([t| Dismantle.PPC.Operand |], [t| (SP.AnyPPC SP.V64) |]) MM.BigEndian)
