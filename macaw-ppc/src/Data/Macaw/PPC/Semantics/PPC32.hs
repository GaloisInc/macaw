{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-unused-matches #-}
module Data.Macaw.PPC.Semantics.PPC32
  ( execInstruction
  ) where

import           Data.Proxy ( Proxy(..) )
import           Dismantle.PPC
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import           SemMC.Architecture.PPC32 ( PPC )
import           SemMC.Architecture.PPC32.Opcodes ( allSemantics, allOpcodeInfo, allDefinedFunctions )

import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.SemMC.TH ( genExecInstruction )
import           Data.Macaw.PPC.Arch ( ppcInstructionMatcher )
import           Data.Macaw.PPC.PPCReg ( locToRegTH )
import           Data.Macaw.PPC.Semantics.TH ( ppcAppEvaluator, ppcNonceAppEval )

execInstruction :: MC.Value PPC ids (MT.BVType 32) -> Instruction -> Maybe (Generator PPC ids s ())
execInstruction = $(genExecInstruction (Proxy @PPC) (locToRegTH (Proxy @PPC))
                    ppcNonceAppEval
                    ppcAppEvaluator
                    'ppcInstructionMatcher
                    allSemantics allOpcodeInfo allDefinedFunctions
                    ([t| Dismantle.PPC.Operand |], [t| PPC |])
                   )
