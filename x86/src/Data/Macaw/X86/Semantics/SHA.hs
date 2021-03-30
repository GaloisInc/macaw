{-# LANGUAGE MultiWayIf, GADTs, RankNTypes, DataKinds, TypeApplications #-}

module Data.Macaw.X86.Semantics.SHA (all_instructions) where

import qualified Flexdis86 as F

import Data.Type.Equality

import Data.Macaw.Types

import Data.Macaw.X86.InstructionDef
import Data.Macaw.X86.Getters
import Data.Macaw.X86.Monad

type DWord ids = Expr ids (BVType 32)
type SHAState ids = (DWord ids, DWord ids, DWord ids, DWord ids, DWord ids, DWord ids, DWord ids, DWord ids)

def_sha256rnds2 :: InstructionDef
def_sha256rnds2 =
  defBinary "sha256rnds2" $ \_ v1 v2 -> do
    SomeBV src1 <- getSomeBVLocation v1
    SomeBV src2 <- getSomeBVLocation v2
    SomeBV xmm0 <- getSomeBVLocation (F.XMMReg $ F.xmmReg 0)
    if | Just Refl <- testEquality (typeWidth src1) (knownNat @128)
       , Just Refl <- testEquality (typeWidth src2) (knownNat @128)
       , Just Refl <- testEquality (typeWidth xmm0) (knownNat @128) -> do
           exp1 <- get src1
           exp2 <- get src2
           x0 <- get xmm0
           let [a, b, e, f] = bvVectorize (knownNat @32) exp2
           let [c, d, g, h] = bvVectorize (knownNat @32) exp1
           let [_, _, w1, w0] = bvVectorize (knownNat @32) x0
           r1 <- sha256rnd w0 (a, b, c, d, e, f, g, h)
           (a2, b2, _c2, _d2, e2, f2, _g2, _h2) <- sha256rnd w1 r1
           src1 .= bvUnvectorize (knownNat @128) [a2 , b2 , e2 , f2]
       | otherwise -> fail "sha256rnds2: bad operand size"
  where
    sha256rnd :: DWord ids -> SHAState ids -> X86Generator st ids (SHAState ids)
    sha256rnd w (a, b, c, d, e, f, g, h) = do
      chefg <- evalArchFn =<< (SHA_Ch <$> eval e <*> eval f <*> eval g)
      majabc <- evalArchFn =<< (SHA_Maj <$> eval a <*> eval b <*> eval c)
      s1e <- evalArchFn . SHA_Sigma1 =<< eval e
      s0a <- evalArchFn . SHA_Sigma0 =<< eval a
      return
        ( chefg .+ s1e .+ w .+ h .+ majabc .+ s0a
        , a
        , b
        , c
        , chefg .+ s1e .+ w .+ h .+ d
        , e
        , f
        , g
        )

def_sha256msg1 :: InstructionDef
def_sha256msg1 =
  defBinary "sha256msg1" $ \_ v1 v2 -> do
    SomeBV src1 <- getSomeBVLocation v1
    SomeBV src2 <- getSomeBVLocation v2
    if | Just Refl <- testEquality (typeWidth src1) (knownNat @128)
       , Just Refl <- testEquality (typeWidth src2) (knownNat @128) -> do
           e1 <- get src1
           e2 <- get src2
           let w4 = bvTrunc (knownNat @32) e2
           let [w3, w2, w1, w0] = bvVectorize (knownNat @32) e1
           res4 <- evalArchFn . SHA_sigma0 =<< eval w4
           res3 <- evalArchFn . SHA_sigma0 =<< eval w3
           res2 <- evalArchFn . SHA_sigma0 =<< eval w2
           res1 <- evalArchFn . SHA_sigma0 =<< eval w1
           src1 .= bvUnvectorize (knownNat @128)
             [ w3 .+ res4
             , w2 .+ res3
             , w1 .+ res2
             , w0 .+ res1
             ]
       | otherwise -> fail "sha256msg1: bad operand size"

def_sha256msg2 :: InstructionDef
def_sha256msg2 =
  defBinary "sha256msg2" $ \_ v1 v2 -> do
    SomeBV src1 <- getSomeBVLocation v1
    SomeBV src2 <- getSomeBVLocation v2
    if | Just Refl <- testEquality (typeWidth src1) (knownNat @128)
       , Just Refl <- testEquality (typeWidth src2) (knownNat @128) -> do
           e1 <- get src1
           e2 <- get src2
           let [w15, w14, _, _] = bvVectorize (knownNat @32) e2
           let [s19, s18, s17, s16] = bvVectorize (knownNat @32) e1
           p14 <- evalArchFn . SHA_sigma1 =<< eval w14
           let w16 = s16 .+ p14
           p15 <- evalArchFn . SHA_sigma1 =<< eval w15
           let w17 = s17 .+ p15
           p16 <- evalArchFn . SHA_sigma1 =<< eval w16
           let w18 = s18 .+ p16
           p17 <- evalArchFn . SHA_sigma1 =<< eval w17
           let w19 = s19 .+ p17
           src1 .= bvUnvectorize (knownNat @128)
             [ w19
             , w18
             , w17
             , w16
             ]
       | otherwise -> fail "sha256msg2: bad operand size"

all_instructions :: [InstructionDef]
all_instructions =
  [ def_sha256rnds2
  , def_sha256msg1
  , def_sha256msg2
  ]
