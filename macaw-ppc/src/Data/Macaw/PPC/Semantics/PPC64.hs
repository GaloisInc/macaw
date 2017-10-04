{-# LANGUAGE TemplateHaskell #-}

module Data.Macaw.PPC.Semantics.PPC64
  ( execInstruction
  ) where

import qualified Dismantle.PPC as D
import qualified Data.Parameterized.Map as Map

import Data.Macaw.PPC.Generator
import Data.Macaw.PPC.Semantics.TH

execInstruction :: D.Instruction -> Maybe (PPCGenerator ppc s ())
execInstruction = $(genExecInstruction Map.empty)
