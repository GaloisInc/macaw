{-# LANGUAGE MultiWayIf, GADTs #-}
{-# LANGUAGE OverloadedStrings #-}

module Data.Macaw.X86.Semantics.ADX (all_instructions) where

import Data.Type.Equality

import Data.Macaw.Types

import Data.Macaw.X86.InstructionDef
import Data.Macaw.X86.Getters
  ( SomeBV(..)
  , getSomeBVLocation
  )
import Data.Macaw.X86.Monad
  ( (.=), (.+)
  , bvLit
  , get
  , mux
  , uadc_overflows

  , cf_loc, of_loc
  )

def_adcx :: InstructionDef
def_adcx = defBinary "adcx" $ \_ v1 v2 -> do
  SomeBV dest <- getSomeBVLocation v1
  SomeBV src <- getSomeBVLocation v2
  let w = typeWidth dest
  if | Just Refl <- testEquality w $ typeWidth src -> do
         x <- get dest
         y <- get src
         c <- get cf_loc
         let cbv = mux c (bvLit w 1) (bvLit w 0)
         cf_loc .= uadc_overflows x y c
         dest .= x .+ y .+ cbv
     | otherwise -> fail "adcx: Unknown bit width"

def_adox :: InstructionDef
def_adox = defBinary "adox" $ \_ v1 v2 -> do
  SomeBV dest <- getSomeBVLocation v1
  SomeBV src <- getSomeBVLocation v2
  let w = typeWidth dest
  if | Just Refl <- testEquality w $ typeWidth src -> do
         x <- get dest
         y <- get src
         o <- get of_loc
         let obv = mux o (bvLit w 1) (bvLit w 0)
         of_loc .= uadc_overflows x y o
         dest .= x .+ y .+ obv
     | otherwise -> fail "adox: Unknown bit width"

all_instructions :: [InstructionDef]
all_instructions =
  [ def_adcx
  , def_adox
  ]
