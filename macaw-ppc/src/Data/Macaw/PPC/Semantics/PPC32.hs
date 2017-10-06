{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
module Data.Macaw.PPC.Semantics.PPC32
  ( execInstruction
  ) where

import qualified Data.Constraint as C
import           Data.Proxy ( Proxy(..) )
import qualified Dismantle.PPC as D
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import           SemMC.Architecture.PPC32 ( PPC )
import           SemMC.Architecture.PPC32.Opcodes ( allSemantics )

import           Data.Macaw.PPC.Generator
import           Data.Macaw.PPC.Semantics.TH ( genExecInstruction )

execInstruction :: MC.Value PPC s (MT.BVType 32) -> D.Instruction -> Maybe (PPCGenerator PPC s ())
execInstruction =  $(genExecInstruction (Proxy @PPC) (C.Sub C.Dict) allSemantics)
