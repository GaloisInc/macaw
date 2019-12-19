{-# LANGUAGE MultiWayIf, GADTs #-}

module Data.Macaw.X86.Semantics.BMI2 (all_instructions) where

import Data.Type.Equality

import Data.Macaw.Types

import Data.Macaw.X86.InstructionDef
import Data.Macaw.X86.Getters
  ( SomeBV(..)
  , getSomeBVLocation
  )
import Data.Macaw.X86.Monad
  ( (.=), (.*)
  , bvSplit
  , get
  , uext

  , rdx, edx
  )

def_mulx :: InstructionDef
def_mulx = defTernary "mulx" $ \_ v1 v2 v3 -> do
  SomeBV high <- getSomeBVLocation v1
  SomeBV low <- getSomeBVLocation v2
  SomeBV l <- getSomeBVLocation v3
  if | Just Refl <- testEquality (typeWidth high) n64
     , Just Refl <- testEquality (typeWidth low) n64
     , Just Refl <- testEquality (typeWidth l) n64
     -> do
         x <- uext n128 <$> get l
         y <- uext n128 <$> get rdx
         let (hr, lr) = bvSplit (x .* y)
         high .= hr
         low .= lr
     | Just Refl <- testEquality (typeWidth high) n32
     , Just Refl <- testEquality (typeWidth low) n32
     , Just Refl <- testEquality (typeWidth l) n32
     -> do
         x <- uext n64 <$> get l
         y <- uext n64 <$> get edx
         let (hr, lr) = bvSplit (x .* y)
         high .= hr
         low .= lr
     | otherwise -> fail "mulx: Unknown bit width"

all_instructions :: [InstructionDef]
all_instructions =
  [ def_mulx
  ]
