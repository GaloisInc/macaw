{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeApplications #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.ARM.Simplify (
  simplifyTruncExt
  ) where

import           Control.Applicative ( (<|>) )
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
                      coalesceAdditionByConstant a
  simplifyArchFn = armSimplifyArchFn

armSimplifyArchFn :: MC.ArchFn ARM.AArch32 (MC.Value ARM.AArch32 ids) tp
                  -> MT.TypeRepr tp
                  -> Maybe (MC.Value ARM.AArch32 ids tp)
armSimplifyArchFn af _rep =
  case af of
    AA.SRem _ z@(MC.BVValue _ 0) _ -> return z
    AA.URem _ z@(MC.BVValue _ 0) _ -> return z
    AA.SDiv _ z@(MC.BVValue _ 0) _ -> return z
    AA.UDiv _ z@(MC.BVValue _ 0) _ -> return z
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
  MC.AssignedValue (MC.Assignment r2_id (MC.EvalApp (MC.BVAdd rep2 r1 constant))) <- return r2
  MC.BVValue constantRepr constantVal <- return constant
  Refl <- testEquality constantRepr (PN.knownNat @65)
  MC.AssignedValue (MC.Assignment r1_id (MC.EvalApp (MC.UExt val rep1))) <- return r1
  Refl <- testEquality rep1 (PN.knownNat @65)
  let MT.BVTypeRepr valwidth = MT.typeRepr val
  case testEquality valwidth targetSize of
    Nothing -> Nothing
    Just Refl -> do
      let newConstant = MC.mkLit targetSize constantVal
      return (MC.BVAdd targetSize val newConstant)

simplifyTrivialTruncExt :: MC.App (MC.Value ARM.AArch32 ids) tp
                        -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyTrivialTruncExt r3 = do
  MC.Trunc r2 rep3 <- return r3
  let targetSize = PN.knownNat @32
  Refl <- testEquality rep3 targetSize
  MC.AssignedValue (MC.Assignment r1_id (MC.EvalApp (MC.UExt val rep1))) <- return r2
  Refl <- testEquality rep1 (PN.knownNat @65)
  let MT.BVTypeRepr valwidth = MT.typeRepr val
  case testEquality valwidth targetSize of
    Nothing -> Nothing
    Just Refl -> do
      let newConstant = MC.BVValue targetSize (PN.toSigned targetSize 0)
      return (MC.BVAdd targetSize val newConstant)

-- | Coalesce adjacent additions by a constant
--
-- > r2 := (bv_add r1 (0xfffffffb :: [65]))
-- > r3 := (bv_add r2 (0x1 :: [65]))
coalesceAdditionByConstant :: MC.App (MC.Value ARM.AArch32 ids) tp
                           -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
coalesceAdditionByConstant r3 = do
  MC.BVAdd rep3 r2 (MC.BVValue bvrep3 c3) <- return r3
  MC.AssignedValue (MC.Assignment _ (MC.EvalApp (MC.BVAdd rep2 r1 (MC.BVValue bvrep2 c2)))) <- return r2
  let newConstant = MC.mkLit bvrep2 (c2 + c3)
  return (MC.BVAdd rep3 r1 newConstant)
