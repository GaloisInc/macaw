{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.SemMC.Simplify (
  SimplifierExtension(..),
  simplifyValue,
  simplifyApp
  ) where

import           Data.Bits
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr ( NatRepr, toSigned, toUnsigned )
import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types ( BVType, BoolType, TypeRepr )

class SimplifierExtension arch where
  -- | This simplifier extension is called before the normal simplifier; if it
  -- returns a simplified term, the normal simplifier is short-circuited.
  simplifyArchApp :: App (Value arch ids) tp -> Maybe (App (Value arch ids) tp)
  simplifyArchFn :: ArchFn arch (Value arch ids) tp -> TypeRepr tp -> Maybe (Value arch ids tp)

-- | A very restricted value simplifier
--
-- The full rewriter is too heavyweight here, as it produces new bound values
-- instead of fully reducing the calculation we want to a literal.
simplifyValue :: ( SimplifierExtension arch
                 , OrdF (ArchReg arch)
                 , MM.MemWidth (ArchAddrWidth arch)
                 )
              => Value arch ids tp
              -> Maybe (Value arch ids tp)
simplifyValue v =
  case v of
    BVValue {} -> Just v
    RelocatableValue {} -> Just v
    AssignedValue (Assignment { assignRhs = EvalApp app }) ->
      simplifyApp app
    AssignedValue (Assignment { assignRhs = EvalArchFn archFn rep }) ->
      simplifyArchFn archFn rep
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
    NotApp (BoolValue False)          -> Just (BoolValue True)
    NotApp (BoolValue True)           -> Just (BoolValue False)
    Mux _ (BoolValue c) t e           -> if c then Just t else Just e
    BVAnd _ l r
      | Just Refl <- testEquality l r -> Just l
    BVAnd sz l r                      -> binopbv (.&.) sz l r
    BVOr  sz l r                      -> binopbv (.|.) sz l r
    BVXor sz l r                      -> binopbv xor sz l r
    BVShl _ l (BVValue _ 0)           -> Just l
    BVShl sz l r                      -> binopbv (\l' r' -> shiftL l' (fromIntegral r')) sz l r
    BVShr _ l (BVValue _ 0)           -> Just l
    BVShr sz l r                      -> binopbv (\l' r' -> shiftR l' (fromIntegral r')) sz l r
    BVSar _ l (BVValue _ 0)           -> Just l
    BVSar sz l r                      -> binopbv (\l' r' ->
                                                   let l'' = toSigned sz l' in
                                                   let r'' = fromIntegral (toSigned sz r') in
                                                   -- Some code will attempt to right-shift by
                                                   -- negative amounts. Prior to GHC 9.0,
                                                   -- `shiftR x y` is always equivalent to
                                                   -- `shiftL x (-y)`, even when `y` is
                                                   -- negative. On GHC 9.0 or later, however,
                                                   -- shifting by negative amounts results in
                                                   -- an arithmetic overflow exception, so we
                                                   -- manually convert negative shift amounts
                                                   -- here to prevent this.
                                                   if r'' >= 0
                                                     then shiftR l'' r''
                                                     else shiftL l'' (-r''))
                                                 sz l r
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
    UExt (RelocatableValue _arep addr) sz -> do
      memword <- MM.asAbsoluteAddr addr
      return $ mkLit sz (fromIntegral memword)
    Trunc (BVValue _ x) sz            -> Just (mkLit sz x)

    Eq l r                            -> boolop (==) l r
    BVComplement sz x                 -> unop complement sz x
    BVSignedLe v1 v2                  -> signedRelOp (<=) v1 v2
    BVSignedLt v1 v2                  -> signedRelOp (<) v1 v2
    BVUnsignedLe v1 v2                -> unsignedRelOp (<=) v1 v2
    BVUnsignedLt v1 v2                -> unsignedRelOp (<) v1 v2
    Mux _ _ t f
      | Just Refl <- testEquality t f -> Just t
    Mux _ c (BoolValue True) (BoolValue False) -> Just c
    Mux _ c (BoolValue False) (BoolValue True) -> simplifyApp (NotApp c)
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
    signedRelOp :: forall n
                 . (Integer -> Integer -> Bool)
                -> Value arch ids (BVType n)
                -> Value arch ids (BVType n)
                -> Maybe (Value arch ids BoolType)
    signedRelOp op (BVValue r1 v1) (BVValue _ v2) =
      Just (BoolValue (op (toSigned r1 v1) (toSigned r1 v2)))
    signedRelOp _ _ _ = Nothing
    unsignedRelOp :: forall n
                   . (Integer -> Integer -> Bool)
                  -> Value arch ids (BVType n)
                  -> Value arch ids (BVType n)
                  -> Maybe (Value arch ids BoolType)
    unsignedRelOp op (BVValue r1 v1) (BVValue _ v2) =
      Just (BoolValue (op (toUnsigned r1 v1) (toUnsigned r1 v2)))
    unsignedRelOp _ _ _ = Nothing
