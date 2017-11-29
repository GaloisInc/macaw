{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-spec-constr -fno-specialise -fmax-simplifier-iterations=1 -fno-call-arity #-}
module Data.Macaw.PPC.Semantics.PPC32
  ( execInstruction
  ) where

import qualified Data.Constraint as C
import           Data.Proxy ( Proxy(..) )
import           Dismantle.PPC
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import           SemMC.Architecture.PPC32 ( PPC )
import           SemMC.Architecture.PPC32.Opcodes ( allSemantics, allOpcodeInfo )

import           Data.Macaw.SemMC.Generator ( Generator )
import           Data.Macaw.PPC.Arch ( ppcInstructionMatcher )
import           Data.Macaw.PPC.PPCReg ( locToRegTH )
import           Data.Macaw.PPC.Semantics.TH ( genExecInstruction )

execInstruction :: MC.Value PPC ids (MT.BVType 32) -> Instruction -> Maybe (Generator PPC ids s ())
execInstruction = $(genExecInstruction (Proxy @PPC) (locToRegTH (Proxy @PPC)) 'ppcInstructionMatcher (C.Sub C.Dict) allSemantics allOpcodeInfo)
