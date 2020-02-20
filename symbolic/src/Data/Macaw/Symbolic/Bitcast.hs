{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.Symbolic.Bitcast (
  doBitcast
  ) where

import           GHC.TypeLits

import           Control.Monad ( forM, when )
import qualified Data.Foldable as F
import qualified Data.Vector as V

import           What4.Interface
import           What4.InterpretedFloatingPoint as C

import           Lang.Crucible.Backend
import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.LLVM.MemModel as MM

import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Types as M

import           Data.Macaw.Symbolic.PersistentState as PS

plus1LeqDbl :: forall n w . (2 <= n, 1 <= w) => NatRepr n -> NatRepr w -> LeqProof (w+1) (n GHC.TypeLits.* w)
plus1LeqDbl n w =
  case testLeq (incNat w) (natMultiply n w) of
    Nothing -> error "Unexpected vector"
    Just p -> p

checkMacawFloatEq :: M.FloatInfoRepr ftp
                  -> FloatInfoToBitWidth (ToCrucibleFloatInfo ftp) :~: M.FloatInfoBits ftp
checkMacawFloatEq f =
  case f of
    M.SingleFloatRepr -> Refl
    M.HalfFloatRepr   -> Refl
    M.DoubleFloatRepr -> Refl
    M.QuadFloatRepr   -> Refl
    M.X86_80FloatRepr -> Refl


doBitcast :: forall sym i o
          .  IsSymInterface sym
          => sym
          -> C.RegValue sym (ToCrucibleType i)
          -> M.WidthEqProof i o
          -> IO (C.RegValue sym (ToCrucibleType o))
doBitcast sym x eqPr =
  case eqPr of
    M.PackBits (n :: NatRepr n) (w :: NatRepr w) -> do
      let outW = natMultiply n w
      LeqProof <- pure $ leqMulPos n w
      LeqProof <- pure $ plus1LeqDbl n w
      when (fromIntegral (V.length x) /= natValue n) $ do
        fail "bitcast: Incorrect input vector length"
      -- We should have at least one element due to constraint on n
      let Just h = x V.!? 0
      let rest :: V.Vector (MM.LLVMPtr sym w)
          rest = V.tail x
      extH <- bvZext sym outW =<< MM.projectLLVM_bv sym h
      let doPack :: (Integer,SymBV sym (n GHC.TypeLits.* w)) -> MM.LLVMPtr sym w -> IO (Integer, SymBV sym (n GHC.TypeLits.* w))
          doPack (i,r) y = do
            extY <- bvZext sym outW =<< MM.projectLLVM_bv sym y
            shiftAmt <- bvLit sym outW i
            r' <- bvOrBits sym r =<< bvShl sym extY shiftAmt
            pure (i+1,r')
      (_,r) <- F.foldlM doPack (1,extH) rest
      MM.llvmPointer_bv sym r
    M.UnpackBits n w -> do
      let inW = natMultiply n w
      LeqProof <- pure $ leqMulPos n w
      LeqProof <- pure $ plus1LeqDbl n w
      xbv <- MM.projectLLVM_bv sym x
      V.generateM (fromIntegral (natValue n)) $ \i -> do
        shiftAmt <- bvLit sym inW (toInteger i)
        MM.llvmPointer_bv sym =<< bvTrunc sym w =<< bvLshr sym xbv shiftAmt
    M.FromFloat f -> do
      Refl <- pure $ checkMacawFloatEq f
      xbv <- C.iFloatToBinary sym (floatInfoToCrucible f) x
      MM.llvmPointer_bv sym xbv
    M.ToFloat f -> do
      xbv <- MM.projectLLVM_bv sym x
      Refl <- pure $ checkMacawFloatEq f
      C.iFloatFromBinary sym (floatInfoToCrucible f) xbv
    M.VecEqCongruence _n eltPr -> do
      forM x $ \e -> doBitcast sym e eltPr
    M.WidthEqRefl _ -> do
      pure x
    M.WidthEqTrans p q -> do
      y <- doBitcast sym x p
      doBitcast sym y q
