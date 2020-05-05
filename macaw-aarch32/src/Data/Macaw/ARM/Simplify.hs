{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.ARM.Simplify (
  simplifyTruncExt
  ) where

import           Control.Applicative ( (<|>) )
import qualified Data.BitVector.Sized as BV
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.SemMC.Simplify as MSS
import qualified Data.Macaw.Types as MT
import           Data.Parameterized.Classes
import qualified Data.Parameterized.NatRepr as PN

import qualified SemMC.Architecture.AArch32 as ARM

import           Data.Macaw.ARM.ARMReg ()
import qualified Data.Macaw.ARM.Arch as AA

instance MSS.SimplifierExtension ARM.AArch32 where
  simplifyArchApp a = simplifyTruncExt a <|>
                      simplifyTrivialTruncExt a <|>
                      coalesceAdditionByConstant a <|>
                      simplifyNestedMux a <|>
                      distributeAddOverConstantMux a <|>
                      doubleNegation a
  simplifyArchFn = armSimplifyArchFn

armSimplifyArchFn :: MC.ArchFn ARM.AArch32 (MC.Value ARM.AArch32 ids) tp
                  -> MT.TypeRepr tp
                  -> Maybe (MC.Value ARM.AArch32 ids tp)
armSimplifyArchFn af _rep =
  case af of
    AA.SRem _ z@(MC.BVValue _ (BV.BV 0)) _ -> return z
    AA.URem _ z@(MC.BVValue _ (BV.BV 0)) _ -> return z
    AA.SDiv _ z@(MC.BVValue _ (BV.BV 0)) _ -> return z
    AA.UDiv _ z@(MC.BVValue _ (BV.BV 0)) _ -> return z
    _ -> Nothing



-- | Simplify terms that extend a pointer, increment it, and then truncate it
-- back to 32 bits.
--
-- These sequences interfere with the abstract interpretation of especially the
-- stack pointer, which just sends any ext/trunc operations to Top.
--
-- > r1 := (uext val 65)
-- > r2 := (bv_add r1 (constant :: [65]))
-- > r3 := (trunc r2 32)
--
-- to (bv_add val (constant :: [32]))
simplifyTruncExt :: MC.App (MC.Value ARM.AArch32 ids) tp
                 -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyTruncExt r3 = do
  MC.Trunc r2 rep3 <- return r3
  let targetSize = PN.knownNat @32
  Refl <- testEquality rep3 targetSize
  MC.AssignedValue (MC.Assignment _r2_id (MC.EvalApp (MC.BVAdd _rep2 r1 constant))) <- return r2
  MC.BVValue constantRepr constantVal <- return constant
  Refl <- testEquality constantRepr (PN.knownNat @65)
  MC.AssignedValue (MC.Assignment _r1_id (MC.EvalApp (MC.UExt val rep1))) <- return r1
  Refl <- testEquality rep1 (PN.knownNat @65)
  let MT.BVTypeRepr valwidth = MT.typeRepr val
  case testEquality valwidth targetSize of
    Nothing -> Nothing
    Just Refl -> do
      let newConstant = MC.BVValue targetSize (BV.trunc targetSize constantVal)
      return (MC.BVAdd targetSize val newConstant)

simplifyTrivialTruncExt :: MC.App (MC.Value ARM.AArch32 ids) tp
                        -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyTrivialTruncExt r3 = do
  MC.Trunc r2 rep3 <- return r3
  let targetSize = PN.knownNat @32
  Refl <- testEquality rep3 targetSize
  MC.AssignedValue (MC.Assignment _r1_id (MC.EvalApp (MC.UExt val rep1))) <- return r2
  Refl <- testEquality rep1 (PN.knownNat @65)
  let MT.BVTypeRepr valwidth = MT.typeRepr val
  case testEquality valwidth targetSize of
    Nothing -> Nothing
    Just Refl -> do
      let newConstant = MC.BVValue targetSize (BV.zero targetSize)
      return (MC.BVAdd targetSize val newConstant)

-- | Coalesce adjacent additions by a constant
--
-- > r2 := (bv_add r1 (0xfffffffb :: [65]))
-- > r3 := (bv_add r2 (0x1 :: [65]))
coalesceAdditionByConstant :: MC.App (MC.Value ARM.AArch32 ids) tp
                           -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
coalesceAdditionByConstant r3 = do
  MC.BVAdd rep3 r2 (MC.BVValue _bvrep3 c3) <- return r3
  MC.AssignedValue (MC.Assignment _ (MC.EvalApp (MC.BVAdd _rep2 r1 (MC.BVValue bvrep2 c2)))) <- return r2
  let newConstant = MC.BVValue bvrep2 (BV.add bvrep2 c2 c3)
  return (MC.BVAdd rep3 r1 newConstant)

-- | Around conditional branches, we generate nested muxes that have the same conditions.
--
-- This code eliminates the redundancy (and happens to make the resulting IP
-- muxes match macaw's expectations to identify conditional branches)
--
-- > r1 := (mux _repr cond1 true1 false1)
-- > r2 := (mux _repr cond2 true2 false2)
-- > r3 := (mux repr cond3 r1 r2)
--
-- If the conditions are all equal, rewrite this into
--
-- > r3 := (mux repr cond3 true1 false2)
simplifyNestedMux :: MC.App (MC.Value ARM.AArch32 ids) tp
                  -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyNestedMux app = do
  MC.Mux repr3 cond3 r1 r2 <- return app
  MC.Mux _repr2 cond2 _true2 false2 <- MC.valueAsApp r2
  MC.Mux _repr1 cond1 true1 _false1 <- MC.valueAsApp r1
  Refl <- testEquality cond1 cond3
  Refl <- testEquality cond2 cond3
  return (MC.Mux repr3 cond3 true1 false2)

withConstantFirst :: MC.Value ARM.AArch32 ids tp
                  -> MC.Value ARM.AArch32 ids tp
                  -> Maybe (MC.Value ARM.AArch32 ids tp, Maybe (MC.App (MC.Value ARM.AArch32 ids) tp))
withConstantFirst l r =
  case (l, r) of
    (MC.BVValue {}, _) -> Just (l, MC.valueAsApp r)
    (_, MC.BVValue {}) -> Just (r, MC.valueAsApp l)
    _ -> Nothing

-- | Distribute an addition over a mux of constant addresses
--
-- There is a common pattern in conditional branches where the branch targets
-- are hidden under a constant addition.  This pushes the addition down.
distributeAddOverConstantMux :: MC.App (MC.Value ARM.AArch32 ids) tp
                             -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
distributeAddOverConstantMux app = do
  MC.BVAdd rep l r <- return app
  Refl <- testEquality rep (PN.knownNat @32)
  (MC.BVValue crep c, Just (MC.Mux mrep cond t f)) <- withConstantFirst l r
  MC.RelocatableValue trep taddr <- return t
  MC.RelocatableValue frep faddr <- return f
  let cval = BV.asSigned crep c
  let taddr' = MC.incAddr cval taddr
  let faddr' = MC.incAddr cval faddr
  return (MC.Mux mrep cond (MC.RelocatableValue trep taddr') (MC.RelocatableValue frep faddr'))

-- Eliminate nested logical negations
doubleNegation :: MC.App (MC.Value ARM.AArch32 ids) tp
               -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
doubleNegation app = do
  MC.NotApp r1 <- return app
  MC.NotApp r2 <- MC.valueAsApp r1
  MC.valueAsApp r2

-- Potentially Normalize negations?
