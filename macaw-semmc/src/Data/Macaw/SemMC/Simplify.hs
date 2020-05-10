{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Macaw.SemMC.Simplify (
  SimplifierExtension(..),
  simplifyValue,
  simplifyApp
  ) where

import qualified Data.BitVector.Sized as BV
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr ( NatRepr )
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
    BVAnd sz l r                      -> binopbv BV.and sz l r
    BVOr  sz l r                      -> binopbv BV.or  sz l r
    BVXor sz l r                      -> binopbv BV.xor sz l r
    BVShl _ l (BVValue _ (BV.BV 0))   -> Just l
    BVShl sz l r                      -> binopbv (\l' r' -> BV.shl sz l' (BV.asNatural r')) sz l r
    BVShr _ l (BVValue _ (BV.BV 0))   -> Just l
    BVShr sz l r                      -> binopbv (\l' r' -> BV.lshr sz l' (BV.asNatural r')) sz l r
    BVSar _ l (BVValue _ (BV.BV 0))   -> Just l
    BVSar sz l r                      -> binopbv (\l' r' -> BV.ashr sz l' (BV.asNatural r')) sz l r
    BVAdd _ l (BVValue _ (BV.BV 0))   -> Just l
    BVAdd _ (BVValue _ (BV.BV 0)) r   -> Just r
    BVAdd rep l@(BVValue {}) r@(RelocatableValue {}) ->
      simplifyApp (BVAdd rep r l)
    BVAdd _rep (RelocatableValue _ addr) (BVValue _ off) ->
      Just (RelocatableValue (addrWidthRepr addr) (MM.incAddr (BV.asUnsigned off) addr))
    BVAdd sz l r                      -> binopbv (BV.add sz) sz l r
    BVMul _ l (BVValue _ (BV.BV 1))   -> Just l
    BVMul _ (BVValue _ (BV.BV 1)) r   -> Just r
    BVMul rep _ (BVValue _ (BV.BV 0)) -> Just (BVValue rep (BV.zero rep))
    BVMul rep (BVValue _ (BV.BV 0)) _ -> Just (BVValue rep (BV.zero rep))
    BVMul rep l r                     -> binopbv (BV.mul rep) rep l r
    SExt (BVValue u n) sz             -> Just (BVValue sz (BV.sext u sz n)) -- (toUnsigned sz (toSigned u n)))
    UExt (BVValue _ n) sz             -> Just (BVValue sz (BV.zext sz n))
    UExt (RelocatableValue _arep addr) sz -> do
      memword <- MM.asAbsoluteAddr addr
      return $ BVValue sz (BV.mkBV sz (toInteger memword))
    Trunc (BVValue _ x) sz            -> Just (BVValue sz (BV.trunc sz x))

    Eq l r                            -> boolop (==) l r
    BVComplement sz x                 -> unop (BV.complement sz) sz x
    BVSignedLe v1 v2                  -> relOp BV.sle v1 v2
    BVSignedLt v1 v2                  -> relOp BV.slt v1 v2
    BVUnsignedLe v1 v2                -> relOp (const BV.ule) v1 v2
    BVUnsignedLt v1 v2                -> relOp (const BV.ult) v1 v2
    Mux _ _ t f
      | Just Refl <- testEquality t f -> Just t
    _                                 -> Nothing
  where
    unop :: forall n . (tp ~ BVType n)
         => (BV.BV n -> BV.BV n)
         -> NatRepr n
         -> Value arch ids tp
         -> Maybe (Value arch ids tp)
    unop f sz (BVValue _ l) = Just (BVValue sz (f l))
    unop _ _ _ = Nothing

    boolop :: (forall n . BV.BV n -> BV.BV n -> Bool)
           -> Value arch ids utp
           -> Value arch ids utp
           -> Maybe (Value arch ids BoolType)
    boolop f (BVValue _ l) (BVValue _ r) =
      Just (BoolValue (f l r))
    boolop _ _ _ = Nothing

    binopbv :: forall n . (tp ~ BVType n)
            => (BV.BV n -> BV.BV n -> BV.BV n)
            -> NatRepr n
            -> Value arch ids tp
            -> Value arch ids tp
            -> Maybe (Value arch ids tp)
    binopbv f sz (BVValue _ l) (BVValue _ r) =
      Just (BVValue sz (f l r))
    binopbv _ _ _ _ = Nothing

    relOp :: forall n .
             (NatRepr n -> BV.BV n -> BV.BV n -> Bool)
          -> Value arch ids (BVType n)
          -> Value arch ids (BVType n)
          -> Maybe (Value arch ids BoolType)
    relOp op (BVValue r1 v1) (BVValue _ v2) =
      Just (BoolValue (op r1 v1 v2))
    relOp _ _ _ = Nothing

    -- signedRelOp :: forall n
    --              . (BV.BV n -> BV.BV n -> Bool)
    --             -> Value arch ids (BVType n)
    --             -> Value arch ids (BVType n)
    --             -> Maybe (Value arch ids BoolType)
    -- signedRelOp op (BVValue r1 v1) (BVValue _ v2) =
    --   Just (BoolValue (op (toSigned r1 v1) (toSigned r1 v2)))
    -- signedRelOp _ _ _ = Nothing

    -- unsignedRelOp :: forall n
    --                . (Integer -> Integer -> Bool)
    --               -> Value arch ids (BVType n)
    --               -> Value arch ids (BVType n)
    --               -> Maybe (Value arch ids BoolType)
    -- unsignedRelOp op (BVValue r1 v1) (BVValue _ v2) =
    --   Just (BoolValue (op (toUnsigned r1 v1) (toUnsigned r1 v2)))
    -- unsignedRelOp _ _ _ = Nothing
