{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Macaw.SemMC.Simplify (
  simplifyValue,
  simplifyApp
  ) where

import           Data.Bits
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr ( NatRepr, toSigned, toUnsigned )
import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types ( BVType, BoolType )

-- | A very restricted value simplifier
--
-- The full rewriter is too heavyweight here, as it produces new bound values
-- instead of fully reducing the calculation we want to a literal.
simplifyValue :: (OrdF (ArchReg arch), MM.MemWidth (ArchAddrWidth arch))
              => Value arch ids tp
              -> Maybe (Value arch ids tp)
simplifyValue v =
  case v of
    BVValue {} -> Just v
    RelocatableValue {} -> Just v
    AssignedValue (Assignment { assignRhs = EvalApp app }) ->
      simplifyApp app
    _ -> Nothing

simplifyApp :: forall arch ids tp
             . (OrdF (ArchReg arch), MM.MemWidth (ArchAddrWidth arch))
            => App (Value arch ids) tp
            -> Maybe (Value arch ids tp)
simplifyApp a =
  case a of
    AndApp (BoolValue True) r         -> Just r
    AndApp l (BoolValue True)         -> Just l
    AndApp f@(BoolValue False) _      -> Just f
    AndApp _ f@(BoolValue False)      -> Just f
    OrApp t@(BoolValue True) _        -> Just t
    OrApp _ t@(BoolValue True)        -> Just t
    OrApp (BoolValue False) r         -> Just r
    OrApp l (BoolValue False)         -> Just l
    Mux _ (BoolValue c) t e           -> if c then Just t else Just e
    BVAnd _ l r
      | Just Refl <- testEquality l r -> Just l
    BVAnd sz l r                      -> binopbv (.&.) sz l r
    BVOr  sz l r                      -> binopbv (.|.) sz l r
    BVShl sz l r                      -> binopbv (\l' r' -> shiftL l' (fromIntegral r')) sz l r
    BVAdd _ l (BVValue _ 0)           -> Just l
    BVAdd _ (BVValue _ 0) r           -> Just r
    BVAdd rep l@(BVValue {}) r@(RelocatableValue {}) ->
      simplifyApp (BVAdd rep r l)
    BVAdd _rep (RelocatableValue _ addr) (BVValue _ off) ->
      Just (RelocatableValue (addrWidthRepr addr) (MM.incAddr off addr))
    BVAdd sz l r                      -> binopbv (+) sz l r
    BVMul _ l (BVValue _ 1)           -> Just l
    BVMul _ (BVValue _ 1) r           -> Just r
    BVMul rep _ (BVValue _ 0)         -> Just (BVValue rep 0)
    BVMul rep (BVValue _ 0) _         -> Just (BVValue rep 0)
    BVMul rep l r                     -> binopbv (*) rep l r
    SExt (BVValue u n) sz             -> Just (BVValue sz (toUnsigned sz (toSigned u n)))
    UExt (BVValue _ n) sz             -> Just (mkLit sz n)
    Trunc (BVValue _ x) sz            -> Just (mkLit sz x)

    Eq l r                            -> boolop (==) l r
    BVComplement sz x                 -> unop complement sz x
    _                                 -> Nothing
  where
    unop :: forall n . (tp ~ BVType n)
         => (Integer -> Integer)
         -> NatRepr n
         -> Value arch ids tp
         -> Maybe (Value arch ids tp)
    unop f sz (BVValue _ l) = Just (mkLit sz (f l))
    unop _ _ _ = Nothing

    boolop :: (Integer -> Integer -> Bool)
           -> Value arch ids utp
           -> Value arch ids utp
           -> Maybe (Value arch ids BoolType)
    boolop f (BVValue _ l) (BVValue _ r) =
      Just (BoolValue (f l r))
    boolop _ _ _ = Nothing

    binopbv :: forall n . (tp ~ BVType n)
            => (Integer -> Integer -> Integer)
            -> NatRepr n
            -> Value arch ids tp
            -> Value arch ids tp
            -> Maybe (Value arch ids tp)
    binopbv f sz (BVValue _ l) (BVValue _ r) =
      Just (mkLit sz (f l r))
    binopbv _ _ _ _ = Nothing
