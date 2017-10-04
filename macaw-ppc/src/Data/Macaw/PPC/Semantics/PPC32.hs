module Data.Macaw.PPC.Semantics.PPC32
  ( execInstruction
  ) where

import qualified Dismantle.PPC as D

import Data.Macaw.PPC.Generator

execInstruction :: D.Instruction -> Maybe (PPCGenerator ppc s ())
execInstruction = undefined
