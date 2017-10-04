{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}
module Data.Macaw.PPC.Semantics.PPC32
  ( execInstruction
  ) where

import qualified Dismantle.PPC as D
import qualified Data.Parameterized.Map as MapF
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import           SemMC.Architecture.PPC32 ( PPC )

import           Data.Macaw.PPC.Generator
import           Data.Macaw.PPC.Semantics.TH ( genExecInstruction )

execInstruction :: MC.Value ppc s (MT.BVType 32) -> D.Instruction -> Maybe (PPCGenerator PPC s ())
execInstruction =  $(genExecInstruction MapF.empty)
