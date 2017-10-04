{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TemplateHaskell #-}

module Data.Macaw.PPC.Semantics.PPC64
  ( execInstruction
  ) where

import qualified Dismantle.PPC as D
import qualified Data.Parameterized.Map as Map
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import           SemMC.Architecture.PPC64 ( PPC )

import           Data.Macaw.PPC.Generator
import           Data.Macaw.PPC.Semantics.TH

execInstruction :: MC.Value ppc s (MT.BVType 64) -> D.Instruction -> Maybe (PPCGenerator PPC s ())
execInstruction = $(genExecInstruction Map.empty)
