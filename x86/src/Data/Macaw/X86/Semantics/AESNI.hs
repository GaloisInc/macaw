{-# LANGUAGE MultiWayIf, GADTs, RankNTypes, DataKinds, TypeApplications #-}

module Data.Macaw.X86.Semantics.AESNI (all_instructions) where

import qualified Flexdis86 as F

import Data.Type.Equality

import Data.Macaw.Types

import Data.Macaw.X86.InstructionDef
import Data.Macaw.X86.Getters
import Data.Macaw.X86.Monad

def_aesni
  :: String
  -> (forall f. (f (BVType 128)) -> (f (BVType 128)) -> X86PrimFn f (BVType 128))
  -> InstructionDef
def_aesni n op =
  defBinary n $ \_ v1 v2 -> do
    SomeBV state <- getSomeBVLocation v1
    SomeBV key <- getSomeBVLocation v2
    if | Just Refl <- testEquality (typeWidth state) (knownNat @128)
       , Just Refl <- testEquality (typeWidth key) (knownNat @128) -> do
           s <- eval =<< get state
           k <- eval =<< get key
           res <- evalArchFn $ op s k
           state .= res
       | otherwise -> fail $ n ++ ": State and key must be 128-bit"

def_aeskeygenassist :: InstructionDef
def_aeskeygenassist =
  defTernary "aeskeygenassist" $ \_ vdest vsrc vimm -> do
    SomeBV dest <- getSomeBVLocation vdest
    SomeBV src <- getSomeBVLocation vsrc
    if | Just Refl <- testEquality (typeWidth dest) n128
       , Just Refl <- testEquality (typeWidth src) n128
       , F.ByteImm k <- vimm -> do
           s <- eval =<< get src
           res <- evalArchFn (AESNI_AESKeyGenAssist s k)
           dest .= res
       | otherwise -> fail "aeskeygenassist: Invalid operands"

def_pclmulqdq :: InstructionDef
def_pclmulqdq =
  defTernaryLVV "pclmulqdq" $ \dest src2 imm -> do
    src1 <- get dest
    if | Just Refl <- testEquality (typeWidth src1) n128
       , Just Refl <- testEquality (typeWidth src2) n128
       , Just Refl <- testEquality (typeWidth imm) n8 -> do
           let (src1h, src1l) = bvSplit src1
           let (src2h, src2l) = bvSplit src2
           temp1 <- eval $ mux (bvBit imm $ bvLit (typeWidth imm) 0) src2h src2l
           temp2 <- eval $ mux (bvBit imm $ bvLit (typeWidth imm) 4) src1h src1l
           res <- evalArchFn (CLMul temp1 temp2)
           dest .= res
       | otherwise -> fail "pclmulqdq: Operands must be 128-bit"

all_instructions :: [InstructionDef]
all_instructions =
  [ def_aesni "aesenc" AESNI_AESEnc
  , def_aesni "aesenclast" AESNI_AESEncLast
  , def_aesni "aesdec" AESNI_AESDec
  , def_aesni "aesdeclast" AESNI_AESDecLast
  , def_aeskeygenassist
  , def_pclmulqdq
  ]
