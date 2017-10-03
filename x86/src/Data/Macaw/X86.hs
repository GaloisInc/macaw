{-
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the primitives needed to provide architecture info for
x86_64 programs.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
module Data.Macaw.X86
       ( x86_64_freeBSD_info
       , x86_64_linux_info
       , freeBSD_syscallPersonality
       , linux_syscallPersonality
         -- * Low level exports
       , ExploreLoc
       , rootLoc
       , disassembleBlock
       , X86TranslateError(..)
       ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad.Cont
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Bits
import qualified Data.Foldable as Fold
import qualified Data.Map as Map
import           Data.Maybe
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import           Data.Word
import qualified Flexdis86 as F
import           Text.PrettyPrint.ANSI.Leijen (Pretty(..), text)

import           Data.Macaw.AbsDomain.AbsState
       ( AbsBlockState
       , setAbsIP
       , absRegState
       , StackEntry(..)
       , concreteStackOffset
       , AbsValue(..)
       , top
       , stridedInterval
       , asConcreteSingleton
       , startAbsStack
       , hasMaximum
       , AbsProcessorState
       , transferValue
       , CallParams(..)
       , absEvalCall
       )
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import           Data.Macaw.Architecture.Info
import           Data.Macaw.Architecture.Syscall
import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
--import           Data.Macaw.Discovery.State
--import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Memory
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types
  ( BoolType
  , BVType
  , TypeRepr(..)
  , knownType
  , n1
  , n8
  , n32
  , n64
  , n128
  , HasRepr(..)
  , typeWidth
  )
import           Data.Macaw.X86.ArchTypes
import           Data.Macaw.X86.Flexdis
import           Data.Macaw.X86.Monad ( bvLit )
import qualified Data.Macaw.X86.Monad as S
import           Data.Macaw.X86.Semantics (execInstruction)
import           Data.Macaw.X86.SyscallInfo.FreeBSD as FreeBSD
import           Data.Macaw.X86.SyscallInfo.Linux as Linux
import           Data.Macaw.X86.X86Reg

------------------------------------------------------------------------
-- Expr

-- | A pure expression for isValue.
data Expr ids tp where
  -- An expression obtained from some value.
  ValueExpr :: !(Value X86_64 ids tp) -> Expr ids tp
  -- An expression that is computed from evaluating subexpressions.
  AppExpr :: !(App (Expr ids) tp) -> Expr ids tp

instance Show (Expr ids tp) where
  show (ValueExpr v) = show v
  show AppExpr{} = "app"

instance MapF.ShowF (Expr ids) where
  showF = show

instance Eq (Expr ids tp) where
  (==) = \x y -> isJust (testEquality x y)

instance TestEquality (Expr ids) where
  testEquality (ValueExpr x) (ValueExpr y) = do
    Refl <- testEquality x y
    return Refl
  testEquality (AppExpr x) (AppExpr y) = do
    Refl <- testEquality x y
    return Refl
  testEquality _ _ = Nothing

asApp :: Expr ids tp -> Maybe (App (Expr ids) tp)
asApp (AppExpr   a) = Just a
asApp (ValueExpr v) = fmapFC ValueExpr <$> valueAsApp v

asArchFn :: Expr ids tp -> Maybe (X86PrimFn (Value X86_64 ids) tp)
asArchFn (ValueExpr (AssignedValue (Assignment _ (EvalArchFn a _)))) = Just a
asArchFn _ = Nothing

app :: App (Expr ids) tp -> (Expr ids) tp
app = AppExpr

instance HasRepr (Expr ids) TypeRepr where
  typeRepr (ValueExpr v) = typeRepr v
  typeRepr (AppExpr a) = typeRepr a

asBoolLit :: Expr ids BoolType -> Maybe Bool
asBoolLit (ValueExpr (BoolValue b)) = Just b
asBoolLit _ = Nothing

asBVLit :: Expr ids (BVType w) -> Maybe Integer
asBVLit (ValueExpr (BVValue _ v)) = Just v
asBVLit _ = Nothing

ltProof :: forall f n m . (n+1 <= m) => f n -> f m -> LeqProof n m
ltProof _ _ = leqTrans lt LeqProof
  where lt :: LeqProof n (n+1)
        lt = leqAdd LeqProof n1

bvSle :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvSle x y = app (BVSignedLe x y)

bvUle :: (1 <= n) => Expr ids (BVType n) -> Expr ids (BVType n) -> Expr ids BoolType
bvUle x y = app (BVUnsignedLe x y)

instance S.IsValue (Expr ids) where

  bv_width = typeWidth

  mux c x y
    | Just True  <- asBoolLit c = x
    | Just False <- asBoolLit c = y
    | x == y = x
    | Just (NotApp cn) <- asApp c = S.mux cn y x
    | otherwise = app $ Mux (typeRepr x) c x y

  boolValue b = ValueExpr (BoolValue b)

  bvLit n v = ValueExpr $ mkLit n (toInteger v)
  bvAdd x y
      -- Eliminate add 0
    | Just 0 <- asBVLit y = x
    | Just 0 <- asBVLit x = y

      -- Constant folding.
    | ValueExpr (BVValue w xv) <- x
    , Just yv <- asBVLit y
    = bvLit w (xv + yv)

    | ValueExpr (RelocatableValue w a) <- x
    , Just o <- asBVLit y
    = ValueExpr (RelocatableValue w (a & incAddr (fromInteger o)))

    | ValueExpr (RelocatableValue w a) <- y
    , Just o <- asBVLit x
    = ValueExpr (RelocatableValue w (a & incAddr (fromInteger o)))

      -- Shift constants to right-hand-side.
    | Just _ <- asBVLit x = S.bvAdd y x

      -- Reorganize addition by constant to offset.
    | Just (BVAdd w x_base (asBVLit -> Just x_off)) <- asApp x
    , Just y_off <- asBVLit y
    = S.bvAdd x_base (bvLit w (x_off + y_off))

    | Just (BVAdd w y_base (asBVLit -> Just y_off)) <- asApp y
    , Just x_off <- asBVLit x
    = S.bvAdd y_base (bvLit w (x_off + y_off))

    | otherwise = app $ BVAdd (typeWidth x) x y

  bvSub x y
    | Just yv <- asBVLit y = S.bvAdd x (bvLit (typeWidth x) (negate yv))
    | otherwise = app $ BVSub (typeWidth x) x y

  bvMul x y
    | Just 0 <- asBVLit x = x
    | Just 1 <- asBVLit x = y
    | Just 0 <- asBVLit y = y
    | Just 1 <- asBVLit y = x

    | Just xv <- asBVLit x, Just yv <- asBVLit y =
      bvLit (typeWidth x) (xv * yv)
    | otherwise = app $ BVMul (typeWidth x) x y

  boolNot x
    | Just xv <- asBoolLit x = S.boolValue (not xv)
      -- not (y < z) = y >= z = z <= y
    | Just (BVUnsignedLt y z) <- asApp x = bvUle z y
      -- not (y <= z) = y > z = z < y
    | Just (BVUnsignedLe y z) <- asApp x = S.bvUlt z y
      -- not (y < z) = y >= z = z <= y
    | Just (BVSignedLt y z) <- asApp x = bvSle z y
      -- not (y <= z) = y > z = z < y
    | Just (BVSignedLe y z) <- asApp x = S.bvSlt z y
      -- not (not p) = p
    | Just (NotApp y) <- asApp x = y
    | otherwise = app $ NotApp x

  bvComplement x
    | Just xv <- asBVLit x = bvLit (typeWidth x) (complement xv)
      -- not (not p) = p
    | Just (BVComplement _ y) <- asApp x = y
    | otherwise = app $ BVComplement (typeWidth x) x

  boolAnd x y
    | Just True  <- asBoolLit x = y
    | Just False <- asBoolLit x = x
    | Just True  <- asBoolLit y = x
    | Just False <- asBoolLit y = y
       -- Idempotence
    | x == y = x

      -- x1 <= x2 & x1 ~= x2 = x1 < x2
    | Just (BVUnsignedLe x1 x2) <- asApp x
    , Just (NotApp yc) <- asApp y
    , Just (Eq y1 y2) <- asApp yc
    , BVTypeRepr w <- typeRepr y1
    , Just Refl <- testEquality (typeWidth x1) w
    , ((x1,x2) == (y1,y2) || (x1,x2) == (y2,y1)) =
      S.bvUlt x1 x2

      -- x1 ~= x2 & x1 <= x2 => x1 < x2
    | Just (BVUnsignedLe y1 y2) <- asApp y
    , Just (NotApp xc) <- asApp x
    , Just (Eq x1 x2) <- asApp xc
    , BVTypeRepr w <- typeRepr x1
    , Just Refl <- testEquality w (typeWidth y1)
    , ((x1,x2) == (y1,y2) || (x1,x2) == (y2,y1)) =
      S.bvUlt y1 y2
      -- Default case
    | otherwise = app $ AndApp x y

  x .&. y
    | Just xv <- asBVLit x, Just yv <- asBVLit y =
      bvLit (typeWidth x) (xv .&. yv)
      -- Eliminate and when one argument is maxUnsigned
    | Just xv <- asBVLit x, xv == maxUnsigned (typeWidth x) = y
    | Just yv <- asBVLit y, yv == maxUnsigned (typeWidth x) = x
      -- Cancel when and with 0.
    | Just 0 <- asBVLit x = x
    | Just 0 <- asBVLit y = y
      -- Idempotence
    | x == y = x

      -- Make literal the second argument (simplifies later cases)
    | isJust (asBVLit x) = assert (isNothing (asBVLit y)) $ y S..&. x

      --(x1 .&. x2) .&. y = x1 .&. (x2 .&. y) -- Only apply when x2 and y is a lit
    | isJust (asBVLit y)
    , Just (BVAnd _ x1 x2) <- asApp x
    , isJust (asBVLit x2) =
      x1 S..&. (x2 S..&. y)

      -- (x1 .|. x2) .&. y = (x1 .&. y) .|. (x2 .&. y) -- Only apply when y and x2 is a lit.
    | isJust (asBVLit y)
    , Just (BVOr _ x1 x2) <- asApp x
    ,  isJust (asBVLit x2) =
      (x1 S..&. y) S..|. (x2 S..&. y)
      -- x .&. (y1 .|. y2) = (y1 .&. x) .|. (y2 .&. x) -- Only apply when x and y2 is a lit.
    | isJust (asBVLit x)
    , Just (BVOr _ y1 y2) <- asApp y
    , isJust (asBVLit y2) =
      (y1 S..&. x) S..|. (y2 S..&. x)

      -- Default case
    | otherwise = app $ BVAnd (typeWidth x) x y

  boolOr x y
    | Just True  <- asBoolLit x = x
    | Just False <- asBoolLit x = y
    | Just True  <- asBoolLit y = y
    | Just False <- asBoolLit y = x
       -- Idempotence
    | x == y = x

      -- Rewrite "x < y | x == y" to "x <= y"
    | Just (BVUnsignedLt x1 x2) <- asApp x
    , Just (Eq y1 y2) <- asApp y
    , BVTypeRepr w <- typeRepr y1
    , Just Refl <- testEquality (typeWidth x1) w
    , (x1,x2) == (y1,y2) || (x1,x2) == (y2,y1)
    = bvUle x1 x2

      -- Default case
    | otherwise = app $ OrApp x y

  x .|. y
    | Just xv <- asBVLit x, Just yv <- asBVLit y =
      bvLit (typeWidth x) (xv .|. yv)
      -- Cancel or when one argument is maxUnsigned
    | Just xv <- asBVLit x, xv == maxUnsigned (typeWidth x) = x
    | Just yv <- asBVLit y, yv == maxUnsigned (typeWidth x) = y
      -- Eliminate "or" when one argument is 0
    | Just 0 <- asBVLit x = y
    | Just 0 <- asBVLit y = x
      -- Idempotence
    | x == y = x

      -- Default case
    | otherwise = app $ BVOr (typeWidth x) x y

  boolXor x y
      -- Eliminate xor with 0.
    | Just False <- asBoolLit x = y
    | Just True  <- asBoolLit x = S.boolNot y
    | Just False <- asBoolLit y = x
    | Just True  <- asBoolLit y = S.boolNot x
      -- Eliminate xor with self.
    | x == y = S.false
      -- If this is a single bit comparison with a constant, resolve to Boolean operation.
      -- Default case.
    | otherwise = app $ XorApp x y

  bvXor x y
      -- Eliminate xor with 0.
    | Just 0 <- asBVLit x = y
    | Just 0 <- asBVLit y = x
      -- Eliminate xor with self.
    | x == y = bvLit (typeWidth x) (0::Integer)
      -- If this is a single bit comparison with a constant, resolve to Boolean operation.
    | ValueExpr (BVValue w v) <- y
    , Just Refl <- testEquality w n1 =
      if v /= 0 then S.bvComplement x else x
      -- Default case.
    | otherwise = app $ BVXor (typeWidth x) x y

  boolEq x y
    | Just True  <- asBoolLit x = y
    | Just False <- asBoolLit x = y
    | Just True  <- asBoolLit y = y
    | Just False <- asBoolLit y = y
    | x == y = S.true
      -- General case
    | otherwise = app $ Eq x y

  x .=. y
    | x == y = S.true
      -- Statically resolve two literals
    | Just xv <- asBVLit x, Just yv <- asBVLit y = S.boolValue (xv == yv)
      -- Move constant to second argument (We implicitly know both x and y are not a constant due to previous case).
    | Just _ <- asBVLit x, Nothing <- asBVLit y = y S..=. x
      -- Rewrite "base + offset = constant" to "base = constant - offset".
    | Just (BVAdd w x_base (asBVLit -> Just x_off)) <- asApp x
    , Just yv <- asBVLit y =
      app $ Eq x_base (bvLit w (yv - x_off))
      -- Rewrite "u - v == c" to "u = c + v".
    | Just (BVSub _ x_1 x_2) <- asApp x = x_1 S..=. S.bvAdd y x_2
      -- Rewrite "c == u - v" to "u = c + v".
    | Just (BVSub _ y_1 y_2) <- asApp y = y_1 S..=. S.bvAdd x y_2
      -- General case
    | otherwise = app $ Eq x y

  -- | Shifts, the semantics is undefined for shifts >= the width of the first argument
  -- bvShr, bvSar, bvShl :: v (BVType n) -> v (BVType log_n) -> v (BVType n)
  bvShr x y
    | Just 0 <- asBVLit y = x
    | Just 0 <- asBVLit x = x
    | otherwise = app $ BVShr (typeWidth x) x y
  bvSar x y = app $ BVSar (typeWidth x) x y

  bvShl x y
    | Just 0 <- asBVLit y = x

    | Just xv <- asBVLit x
    , Just yv <- asBVLit y =
      assert (yv <= toInteger (maxBound :: Int)) $
        bvLit (typeWidth x) (xv `shiftL` fromInteger yv)

      -- Replace "(x >> c) << c" with (x .&. - 2^c)
    | Just yv <- asBVLit y
    , Just (BVShr w x_base (asBVLit -> Just x_shft)) <- asApp x
    , x_shft == yv =
      x_base S..&. bvLit w (negate (2^x_shft) ::Integer)

    | Just yv <- asBVLit y
    , yv >= natValue (typeWidth x) = bvLit (typeWidth x) (0 :: Integer)

    | otherwise = app $ BVShl (typeWidth x) x y

  bvTrunc' w e0
    | Just v <- asBVLit e0 =
      bvLit w v
    | Just Refl <- testEquality (typeWidth e0) w =
      e0
    | Just (MMXExtend e) <- asArchFn e0
    , Just Refl <- testEquality w n64 =
      ValueExpr e
    | Just (UExt e _) <- asApp e0 =
      case testLeq w (S.bv_width e) of
        -- Check if original value width is less than new width.
        Just LeqProof -> S.bvTrunc w e
        Nothing ->
          -- Runtime check to wordaround GHC typechecker
          case testLeq (S.bv_width e) w of
            Just LeqProof -> S.uext w e
            Nothing -> error "bvTrunc internal error"
      -- Trunc (x .&. y) w = trunc x w .&. trunc y w
    | Just (BVAnd _ x y) <- asApp e0 =
      let x' = S.bvTrunc' w x
          y' = S.bvTrunc' w y
       in x' S..&. y'
      -- Trunc (x .|. y) w = trunc x w .|. trunc y w
    | Just (BVOr _ x y) <- asApp e0 =
      let x' = S.bvTrunc' w x
          y' = S.bvTrunc' w y
       in x' S..|. y'
      -- trunc (Trunc e w1) w2 = trunc e w2
    | Just (Trunc e _) <- asApp e0 =
      -- Runtime check to workaround GHC typechecker.
      case testLeq w (typeWidth e) of
        Just LeqProof -> S.bvTrunc w e
        Nothing -> error "bvTrunc given bad width"
      -- Default case
    | otherwise = app (Trunc e0 w)

  bvUlt x y
    | Just xv <- asBVLit x, Just yv <- asBVLit y = S.boolValue (xv < yv)
    | x == y = S.false
    | otherwise =
      case typeRepr x of
        BVTypeRepr _ -> app $ BVUnsignedLt x y

  bvSlt x y
    | Just xv <- asBVLit x, Just yv <- asBVLit y = S.boolValue (xv < yv)
    | x == y = S.false
    | otherwise =
      case typeRepr x of
        BVTypeRepr _ -> app $ BVSignedLt x y

  bvBit x y
    | Just xv <- asBVLit x
    , Just yv <- asBVLit y =
      S.boolValue (xv `testBit` fromInteger yv)
    | Just (Trunc xe w) <- asApp x
    , Just LeqProof <- testLeq n1 (typeWidth xe)
    , Just yv <- asBVLit y = assert (0 <= yv && yv < natValue w) $
      S.bvBit xe y

    | otherwise =
      app $ BVTestBit x y

  sext' w e0
      -- Collapse duplicate extensions.
    | Just (SExt e w0) <- asApp e0 = do
      let we = S.bv_width e
      withLeqProof (leqTrans (ltProof we w0) (ltProof w0 w)) $
        S.sext w e
    | otherwise = app (SExt e0 w)

  uext' w e0
      -- Literal case
    | Just v <- asBVLit e0 =
      let w0 = S.bv_width e0
       in withLeqProof (leqTrans (leqProof n1 w0) (ltProof w0 w)) $
            bvLit w v
      -- Collapse duplicate extensions.
    | Just (UExt e w0) <- asApp e0 = do
      let we = S.bv_width e
      withLeqProof (leqTrans (ltProof we w0) (ltProof w0 w)) $
        S.uext w e

      -- Default case
    | otherwise = app (UExt e0 w)

  even_parity x
    | Just xv <- asBVLit x =
        let go 8 r = r
            go i r = go (i+1) $! (xv `testBit` i /= r)
         in S.boolValue (go 0 True)
    | otherwise = app $ EvenParity x
  reverse_bytes x = app $ ReverseBytes (typeWidth x) x

  uadc_overflows x y c
    | Just 0 <- asBVLit y, Just False <- asBoolLit c = S.false
    | otherwise = app $ UadcOverflows (typeWidth x) x y c
  sadc_overflows x y c
    | Just 0 <- asBVLit y, Just False <- asBoolLit c = S.false
    | otherwise = app $ SadcOverflows (typeWidth x) x y c

  usbb_overflows x y c
    | Just 0 <- asBVLit y, Just False <- asBoolLit c = S.false
      -- If the borrow bit is zero, this is equivalent to unsigned x < y.
    | Just False <- asBoolLit c = S.bvUlt x y
    | otherwise = app $ UsbbOverflows (typeWidth x) x y c

  ssbb_overflows x y c
    | Just 0 <- asBVLit y, Just False <- asBoolLit c = S.false
      -- If the borrow bit is zero, this is equivalent to signed x < y.
      -- FIXME: not true? | Just 0 <- asBVLit c = app $ BVSignedLt x y
    | otherwise = app $ SsbbOverflows (typeWidth x) x y c

  bsf x = app $ Bsf (typeWidth x) x
  bsr x = app $ Bsr (typeWidth x) x

  isQNaN rep x = app $ FPIsQNaN rep x
  isSNaN rep x = app $ FPIsSNaN rep x

  fpAdd rep x y = app $ FPAdd rep x y
  fpAddRoundedUp rep x y = app $ FPAddRoundedUp rep x y

  fpSub rep x y = app $ FPSub rep x y
  fpSubRoundedUp rep x y = app $ FPSubRoundedUp rep x y

  fpMul rep x y = app $ FPMul rep x y
  fpMulRoundedUp rep x y = app $ FPMulRoundedUp rep x y

  fpDiv rep x y = app $ FPDiv rep x y

  fpLt rep x y = app $ FPLt rep x y
  fpEq rep x y = app $ FPEq rep x y

  fpCvt src tgt x =
    case testEquality src tgt of
      Just Refl -> x
      _ -> app $ FPCvt src x tgt
  fpCvtRoundsUp src tgt x = app $ FPCvtRoundsUp src x tgt

  fpFromBV tgt x = app $ FPFromBV x tgt
  truncFPToSignedBV tgt src x = app $ TruncFPToSignedBV src x tgt

------------------------------------------------------------------------
-- PreBlock

-- | A block that we have not yet finished.
data PreBlock ids = PreBlock { pBlockIndex :: !Word64
                             , pBlockAddr  :: !(MemSegmentOff 64)
                               -- ^ Starting address of function in preblock.
                             , _pBlockStmts :: !(Seq (Stmt X86_64 ids))
                             , _pBlockState :: !(RegState X86Reg (Value X86_64 ids))
                             , _pBlockApps  :: !(MapF (App (Value X86_64 ids)) (Assignment X86_64 ids))
                             }

-- | Create a new pre block.
emptyPreBlock :: RegState X86Reg (Value X86_64 ids)
              -> Word64
              -> MemSegmentOff 64
              -> PreBlock ids
emptyPreBlock s idx addr =
  PreBlock { pBlockIndex  = idx
           , pBlockAddr   = addr
           , _pBlockStmts = Seq.empty
           , _pBlockApps  = MapF.empty
           , _pBlockState = s
           }

pBlockStmts :: Simple Lens (PreBlock ids) (Seq (Stmt X86_64 ids))
pBlockStmts = lens _pBlockStmts (\s v -> s { _pBlockStmts = v })

pBlockState :: Simple Lens (PreBlock ids) (RegState X86Reg (Value X86_64 ids))
pBlockState = lens _pBlockState (\s v -> s { _pBlockState = v })

pBlockApps  :: Simple Lens (PreBlock ids) (MapF (App (Value X86_64 ids)) (Assignment X86_64 ids))
pBlockApps = lens _pBlockApps (\s v -> s { _pBlockApps = v })

------------------------------------------------------------------------
-- BlockSeq

-- | List of blocks generated so far, and an index for generating new block labels.
data BlockSeq ids  = BlockSeq
       { _nextBlockID  :: !Word64
         -- ^ Index of next block
       , _frontierBlocks :: !(Seq (Block X86_64 ids))
         -- ^ Blocks added to CFG
       }

-- | Control flow blocs generated so far.
nextBlockID :: Simple Lens (BlockSeq ids) Word64
nextBlockID = lens _nextBlockID (\s v -> s { _nextBlockID = v })

-- | Blocks that are not in CFG that end with a FetchAndExecute,
-- which we need to analyze to compute new potential branch targets.
frontierBlocks :: Simple Lens (BlockSeq ids) (Seq (Block X86_64 ids))
frontierBlocks = lens _frontierBlocks (\s v -> s { _frontierBlocks = v })

------------------------------------------------------------------------
-- GenResult

-- | The final result from the block generator.
data GenResult ids = GenResult { resBlockSeq :: !(BlockSeq ids)
                               , resState :: !(Maybe (PreBlock ids))
                               }

------------------------------------------------------------------------
-- GenState

-- | A state used for the block generator.
data GenState st_s ids = GenState
       { assignIdGen   :: !(NonceGenerator (ST st_s) ids)
         -- ^ 'NonceGenerator' for generating 'AssignId's
       , _blockSeq     :: !(BlockSeq ids)
         -- ^ Blocks generated so far.
       , _blockState   :: !(PreBlock ids)
         -- ^ Current block
       , genAddr      :: !(MemSegmentOff 64)
         -- ^ Address of current instruction we are disassmebling
       }

-- | Create a gen result from a state result.
mkGenResult :: GenState st_s ids -> GenResult ids
mkGenResult s = GenResult { resBlockSeq = s^.blockSeq
                          , resState = Just (s^.blockState)
                          }

-- | Control flow blocs generated so far.
blockSeq :: Simple Lens (GenState st_s ids) (BlockSeq ids)
blockSeq = lens _blockSeq (\s v -> s { _blockSeq = v })

-- | Blocks that are not in CFG that end with a FetchAndExecute,
-- which we need to analyze to compute new potential branch targets.
blockState :: Lens (GenState st_s ids) (GenState st_s ids) (PreBlock ids) (PreBlock ids)
blockState = lens _blockState (\s v -> s { _blockState = v })

curX86State :: Simple Lens (GenState st_s ids) (RegState X86Reg (Value X86_64 ids))
curX86State = blockState . pBlockState

-- | Finishes the current block, if it is started.
finishBlock' :: PreBlock ids
             -> (RegState X86Reg (Value X86_64 ids) -> TermStmt X86_64 ids)
             -> Block X86_64 ids
finishBlock' pre_b term =
  Block { blockLabel = pBlockIndex pre_b
        , blockAddr  = pBlockAddr pre_b
        , blockStmts = Fold.toList (pre_b^.pBlockStmts)
        , blockTerm  = term (pre_b^.pBlockState)
        }

-- | Finishes the current block, if it is started.
finishBlock :: (RegState X86Reg (Value X86_64 ids) -> TermStmt X86_64 ids)
            -> GenResult ids
            -> BlockSeq ids
finishBlock term st =
  case resState st of
    Nothing    -> resBlockSeq st
    Just pre_b ->
      let b = finishBlock' pre_b term
       in seq b $ resBlockSeq st & frontierBlocks %~ (Seq.|> b)

------------------------------------------------------------------------
-- X86Generator

-- | X86Generator is used to construct basic blocks from a stream of instructions
-- using the semantics.
--
-- It is implemented as a state monad in a continuation passing style so that
-- we can perform symbolic branches.
--
-- This returns either a failure message or the next state.
newtype X86Generator st_s ids a =
  X86G { unX86G ::
           ContT (GenResult ids)
                 (ReaderT (GenState st_s ids)
                          (ExceptT Text (ST st_s))) a
       }
  deriving (Applicative, Functor)

-- The main reason for this definition to be given explicitly is so that fail
-- uses throwError instead of the underlying fail in ST
instance Monad (X86Generator st_s ids) where
  return v = seq v $ X86G $ return v
  (X86G m) >>= h = X86G $ m >>= \v -> seq v (unX86G (h v))
  X86G m >> X86G n = X86G $ m >> n
  fail msg = seq t $ X86G $ ContT $ \_ -> throwError t
    where t = Text.pack msg

type instance S.Value (X86Generator st_s ids) = Expr ids

-- | The type of an 'X86Generator' continuation
type X86GCont st_s ids a
  =  a
  -> GenState st_s ids
  -> ExceptT Text (ST st_s) (GenResult ids)

-- | Run an 'X86Generator' starting from a given state
runX86Generator :: X86GCont st_s ids a
                -> GenState st_s ids
                -> X86Generator st_s ids a
                -> ExceptT Text (ST st_s) (GenResult ids)
runX86Generator k st (X86G m) = runReaderT (runContT m (ReaderT . k)) st

-- | Capture the current continuation and 'GenState' in an 'X86Generator'
shiftX86GCont :: (X86GCont st_s ids a
                  -> GenState st_s ids
                  -> ExceptT Text (ST st_s) (GenResult ids))
              -> X86Generator st_s ids a
shiftX86GCont f =
  X86G $ ContT $ \k -> ReaderT $ \s -> f (runReaderT . k) s

modGenState :: State (GenState st_s ids) a -> X86Generator st_s ids a
modGenState m = X86G $ ContT $ \c -> ReaderT $ \s ->
  let (a,s') = runState m s
   in runReaderT (c a) s'

modState :: State (RegState X86Reg (Value X86_64 ids)) a -> X86Generator st_s ids a
modState m = modGenState $ do
  s <- use curX86State
  let (r,s') = runState m s
  curX86State .= s'
  return r

-- | Create a new assignment identifier
newAssignID :: X86Generator st_s ids (AssignId ids tp)
newAssignID = do
  gs <- X86G $ ask
  liftM AssignId $ X86G $ lift $ lift $ lift $ freshNonce $ assignIdGen gs

addStmt :: Stmt X86_64 ids -> X86Generator st_s ids ()
addStmt stmt = seq stmt $
  modGenState $ blockState . pBlockStmts %= (Seq.|> stmt)


addAssignment :: AssignRhs X86_64 ids tp
              -> X86Generator st_s ids (Assignment X86_64 ids tp)
addAssignment rhs = do
  l <- newAssignID
  let a = Assignment l rhs
  addStmt $ AssignStmt a
  return a

addArchFn :: X86PrimFn (Value X86_64 ids) tp
          -> X86Generator st_s ids (Assignment X86_64 ids tp)
addArchFn fn = addAssignment (EvalArchFn fn (typeRepr fn))

-- | This function does a top-level constant propagation/constant reduction.
-- We assume that the leaf nodes have also been propagated (i.e., we only operate
-- at the outermost term)

-- FIXME: make less ad-hoc
constPropagate :: forall ids tp. App (Value X86_64 ids) tp -> Maybe (Value X86_64 ids tp)
constPropagate v =
  case v of
   BVAnd _ l r
     | Just _ <- testEquality l r -> Just l
   BVAnd sz l r                   -> binop (.&.) sz l r
   -- Units
   BVAdd _  l (BVValue _ 0)       -> Just l
   BVAdd _  (BVValue _ 0) r       -> Just r
   BVAdd sz l r                   -> binop (+) sz l r
   BVMul _  l (BVValue _ 1)       -> Just l
   BVMul _  (BVValue _ 1) r       -> Just r

   UExt  (BVValue _ n) sz         -> Just $ mkLit sz n

   -- Word operations
   Trunc (BVValue _ x) sz         -> Just $ mkLit sz x

   -- Boolean operations
   BVUnsignedLt l r               -> boolop (<) l r
   Eq l r                         -> boolop (==) l r
   BVComplement sz x              -> unop complement sz x
   _                              -> Nothing
  where
    boolop :: (Integer -> Integer -> Bool)
           -> Value X86_64 ids utp
           -> Value X86_64 ids utp
           -> Maybe (Value X86_64 ids BoolType)
    boolop f (BVValue _ l) (BVValue _ r) = Just $ BoolValue (f l r)
    boolop _ _ _ = Nothing

    unop :: (tp ~ BVType n)
         => (Integer -> Integer)
         -> NatRepr n -> Value X86_64 ids tp -> Maybe (Value X86_64 ids tp)
    unop f sz (BVValue _ l)  = Just $ mkLit sz (f l)
    unop _ _ _               = Nothing

    binop :: (tp ~ BVType n) => (Integer -> Integer -> Integer)
          -> NatRepr n
          -> Value X86_64 ids tp
          -> Value X86_64 ids tp
          -> Maybe (Value X86_64 ids tp)
    binop f sz (BVValue _ l) (BVValue _ r) = Just $ mkLit sz (f l r)
    binop _ _ _ _                          = Nothing

evalApp :: App (Value X86_64 ids) tp -> X86Generator st_s ids (Value X86_64 ids tp)
evalApp a = do
  case constPropagate a of
    Nothing -> do
      m <- modGenState $ use (blockState . pBlockApps)
      case MapF.lookup a m of
        Nothing -> do
          r <- addAssignment (EvalApp a)
          modGenState $ (blockState . pBlockApps) %= MapF.insert a r
          return (AssignedValue r)
        Just r -> return (AssignedValue r)
    Just v  -> return v

eval :: Expr ids tp -> X86Generator st_s ids (Value X86_64 ids tp)
eval (ValueExpr v) = return v
eval (AppExpr a) = evalApp =<< traverseFC eval a

-- | Type for addresses.
type AddrExpr ids = Expr ids (BVType 64)

------------------------------------------------------------------------
-- ExploreLoc

-- | This represents the control-flow information needed to build basic blocks
-- for a code location.
data ExploreLoc
   = ExploreLoc { loc_ip      :: !(MemSegmentOff 64)
                  -- ^ IP address.
                , loc_x87_top :: !Int
                  -- ^ Top register of x87 stack
                , loc_df_flag :: !Bool
                  -- ^ Value of DF flag
                }
 deriving (Eq, Ord)

instance Pretty ExploreLoc where
  pretty loc = text $ show (loc_ip loc)

rootLoc :: MemSegmentOff 64 -> ExploreLoc
rootLoc ip = ExploreLoc { loc_ip      = ip
                        , loc_x87_top = 7
                        , loc_df_flag = False
                        }

initX86State :: ExploreLoc -- ^ Location to explore from.
             -> RegState X86Reg (Value X86_64 ids)
initX86State loc = mkRegState Initial
                 & curIP     .~ RelocatableValue knownNat (relativeSegmentAddr (loc_ip loc))
                 & boundValue X87_TopReg .~ mkLit knownNat (toInteger (loc_x87_top loc))
                 & boundValue DF         .~ BoolValue (loc_df_flag loc)

------------------------------------------------------------------------
-- Location

type ImpLocation ids tp = S.Location (AddrExpr ids) tp

getX87Top :: X86Generator st_s ids Int
getX87Top = do
  top_val <- modState $ use $ boundValue X87_TopReg
  case top_val of
    -- Validate that i is less than top and top +
    BVValue _ (fromInteger -> topv) ->
      return topv
    _ -> fail $ "Unsupported value for top register " ++ show (pretty top_val)

getX87Offset :: Int -> X86Generator st_s ids Int
getX87Offset i = do
  topv <- getX87Top
  unless (0 <= topv + i && topv + i <= 7) $ do
    fail $ "Illegal floating point index"
  return $! topv + i

readLoc :: X86PrimLoc tp -> X86Generator st_s ids (Expr ids tp)
readLoc l = ValueExpr . AssignedValue <$> addArchFn (ReadLoc l)

getLoc :: ImpLocation ids tp -> X86Generator st_s ids (Expr ids tp)
getLoc (l0 :: ImpLocation ids tp) =
  case l0 of
    S.MemoryAddr w tp -> do
      addr <- eval w
      ValueExpr . AssignedValue <$> addAssignment (ReadMem addr tp)
    S.ControlReg _ ->
      fail $ "Do not support writing to control registers."
    S.DebugReg _ ->
      fail $ "Do not support writing to debug registers."
    S.SegmentReg s
      | s == F.FS -> readLoc FS
      | s == F.GS -> readLoc GS
        -- Otherwise registers are 0.
      | otherwise ->
        fail $ "On x86-64 registers other than fs and gs may not be read."
    S.X87ControlReg r ->
      readLoc (X87_ControlLoc r)
    S.FullRegister r -> do
      modState $ ValueExpr <$> use (boundValue r)
    S.Register (rv :: S.RegisterView m b n) -> do
      let r = S.registerViewReg rv
      modState $ S.registerViewRead rv . ValueExpr <$> use (boundValue r)
    -- TODO
    S.X87StackRegister i -> do
      idx <- getX87Offset i
      e <- modState $ use $ boundValue (X87_FPUReg (F.mmxReg (fromIntegral idx)))
      -- TODO: Check tag register is assigned.
      return $! ValueExpr e

addArchStmt :: X86Stmt (Value X86_64 ids) -> X86Generator st_s ids ()
addArchStmt s = addStmt $ ExecArchStmt (X86Stmt s)

addWriteLoc :: X86PrimLoc tp -> Value X86_64 ids tp -> X86Generator st_s ids ()
addWriteLoc l v = addArchStmt $ WriteLoc l v

-- | Assign a value to a location
setLoc :: forall ids st_s tp
       .  ImpLocation ids tp
       -> Value X86_64 ids tp
       -> X86Generator st_s ids ()
setLoc loc v =
  case loc of
   S.MemoryAddr w tp -> do
     addr <- eval w
     addStmt $ WriteMem addr tp v

   S.ControlReg r -> do
     addWriteLoc (ControlLoc r) v
   S.DebugReg r  ->
     addWriteLoc (DebugLoc r) v

   S.SegmentReg s
     | s == F.FS -> addWriteLoc FS v
     | s == F.GS -> addWriteLoc GS v
       -- Otherwise registers are 0.
     | otherwise ->
       fail $ "On x86-64 registers other than fs and gs may not be set."

   S.X87ControlReg r ->
     addWriteLoc (X87_ControlLoc r) v
   S.FullRegister r -> do
     modState $ boundValue r .= v
   S.Register (rv :: S.RegisterView m b n) -> do
     let r = S.registerViewReg rv
     v0 <- modState $ ValueExpr <$> use (boundValue r)
     v1 <- eval $ S.registerViewWrite rv v0 (ValueExpr v)
     modState $ boundValue r .= v1
   S.X87StackRegister i -> do
     off <- getX87Offset i
     modState $ boundValue (X87_FPUReg (F.mmxReg (fromIntegral off))) .= v

instance S.Semantics (X86Generator st_s ids) where
  make_undefined tp =
    ValueExpr . AssignedValue <$> addAssignment (SetUndefined tp)

  -- Get value of a location.
  get = getLoc

  l .= e = setLoc l =<< eval e

  -- Implement ifte_
  -- Note that this implementation will run any code appearing after the ifte_
  -- twice, once for the true branch and once for the false branch.
  --
  -- This could be changed to run the code afterwards once, but the cost would be
  -- defining a way to merge processor states from the different branches, and making
  -- sure that expression assignments generated in one branch were not referred to in
  -- another branch.
  --
  -- One potential design change, not implemented here, would be to run both branches,
  -- up to the point where they merge, and if the resulting PC is in the same location,
  -- to merge in that case, otherwise to run them separately.
  --
  -- This would support the cmov instruction, but result in divergence for branches, which
  -- I think is what we want.
  ifte_ c_expr t f = eval c_expr >>= go
    where
      go (BoolValue True) = t
      go (BoolValue False) = f
      go cond =
        shiftX86GCont $ \c s0 -> do
          let p_b = s0 ^.blockState
          let st = p_b^.pBlockState
          let t_block_label = s0^.blockSeq^.nextBlockID
          let s2 = s0 & blockSeq . nextBlockID +~ 1
                      & blockSeq . frontierBlocks .~ Seq.empty
                      & blockState .~ emptyPreBlock st t_block_label (genAddr s0)
          -- Run true block.
          t_seq <- finishBlock FetchAndExecute <$> runX86Generator c s2 t
          -- Run false block
          let f_block_label = t_seq^.nextBlockID
          let s5 = GenState { assignIdGen = assignIdGen s0
                            , _blockSeq =
                                BlockSeq { _nextBlockID    = t_seq^.nextBlockID + 1
                                         , _frontierBlocks = Seq.empty
                                         }
                            , _blockState = emptyPreBlock st f_block_label (genAddr s0)
                            , genAddr = genAddr s0
                            }
          f_seq <- finishBlock FetchAndExecute <$> runX86Generator c s5 f

          -- Join results together.
          let fin_b = finishBlock' p_b (\_ -> Branch cond t_block_label f_block_label)
          seq fin_b $ do
          return $
            GenResult { resBlockSeq =
                         BlockSeq { _nextBlockID = _nextBlockID f_seq
                                  , _frontierBlocks = (s0^.blockSeq^.frontierBlocks Seq.|> fin_b)
                                               Seq.>< t_seq^.frontierBlocks
                                               Seq.>< f_seq^.frontierBlocks
                                  }
                      , resState = Nothing
                      }

  memcopy val_sz count src dest is_reverse = do
    count_v <- eval count
    src_v   <- eval src
    dest_v  <- eval dest
    is_reverse_v <- eval is_reverse
    addArchStmt $ MemCopy val_sz count_v src_v dest_v is_reverse_v

  memcmp sz count src dest is_reverse = do
    count_v <- eval count
    is_reverse_v <- eval is_reverse
    src_v   <- eval src
    dest_v  <- eval dest
    ValueExpr . AssignedValue
      <$> addArchFn (MemCmp sz count_v src_v dest_v is_reverse_v)

  memset count val dest dfl = do
    count_v <- eval count
    val_v   <- eval val
    dest_v  <- eval dest
    df_v    <- eval dfl
    addArchStmt $ MemSet count_v val_v dest_v df_v

  rep_scas True is_reverse sz val buf count = do
    val_v   <- eval val
    buf_v   <- eval buf
    count_v <- eval count
    is_reverse_v <- eval is_reverse
    case is_reverse_v of
      BoolValue False -> do
        ValueExpr . AssignedValue <$> addArchFn (RepnzScas sz val_v buf_v count_v)
      _ -> do
        fail $ "Unsupported rep_scas value " ++ show is_reverse_v
  rep_scas False _is_reverse _sz _val _buf _count = do
    fail $ "Semantics only currently supports finding elements."

  primitive S.Syscall = do
    shiftX86GCont $ \_ s0 -> do
      -- Get last block.
      let p_b = s0 ^. blockState
      -- Create finished block.
      let fin_b = finishBlock' p_b (ArchTermStmt X86Syscall)
      seq fin_b $ do
      -- Return early
      return $ GenResult { resBlockSeq = s0 ^.blockSeq & frontierBlocks %~ (Seq.|> fin_b)
                         , resState = Nothing
                         }

  primitive S.CPUID = do
    rax_val <- modState $ use $ boundValue RAX
    eax_val <- eval (S.bvTrunc' n32  (ValueExpr rax_val))
    -- Call CPUID and get a 128-bit value back.
    res <- ValueExpr . AssignedValue <$> addArchFn (CPUID eax_val)
    S.eax S..= S.bvTrunc n32 res
    S.ebx S..= S.bvTrunc n32 (res `S.bvShr` bvLit n128 32)
    S.ecx S..= S.bvTrunc n32 (res `S.bvShr` bvLit n128 64)
    S.edx S..= S.bvTrunc n32 (res `S.bvShr` bvLit n128 96)

  primitive S.RDTSC = do
    res <- ValueExpr . AssignedValue <$> addArchFn RDTSC
    S.edx S..= S.bvTrunc n32 (res `S.bvShr` bvLit n64 32)
    S.eax S..= S.bvTrunc n32 res
  primitive S.XGetBV = do
    ecx_val <- eval =<< S.get S.ecx
    res <- ValueExpr . AssignedValue <$> addArchFn (XGetBV ecx_val)
    S.edx S..= S.bvTrunc n32 (res `S.bvShr` bvLit n64 32)
    S.eax S..= S.bvTrunc n32 res

  fnstcw addr = do
    addr_val <- eval addr
    addArchStmt $ StoreX87Control addr_val

  pshufb w x y = do
    x_val <- eval x
    y_val <- eval y
    ValueExpr . AssignedValue <$> addArchFn (PShufb w x_val y_val)

  getSegmentBase seg =
    case seg of
      F.FS -> ValueExpr . AssignedValue <$> addArchFn ReadFSBase
      F.GS -> ValueExpr . AssignedValue <$> addArchFn ReadGSBase
      _ ->
        error $ "X86_64 getSegmentBase " ++ show seg ++ ": unimplemented!"

  bvQuotRem rep n d = do
    nv <- eval n
    dv <- eval d
    q <- ValueExpr . AssignedValue <$> addArchFn (X86Div rep nv dv)
    r <- ValueExpr . AssignedValue <$> addArchFn (X86Rem rep nv dv)
    pure (q,r)

  bvSignedQuotRem rep n d = do
    nv <- eval n
    dv <- eval d
    q <- ValueExpr . AssignedValue <$> addArchFn (X86IDiv rep nv dv)
    r <- ValueExpr . AssignedValue <$> addArchFn (X86IRem rep nv dv)
    pure (q,r)

  -- exception :: Value m BoolType    -- mask
  --            -> Value m BoolType -- predicate
  --            -> ExceptionClass
  --            -> m ()
  exception m p c = do
    S.when_ (S.boolNot m S..&&. p)
            (addStmt (PlaceHolderStmt [] $ "Exception " ++ (show c)))

  x87Push e = do
    v <- eval e
    topv <- getX87Top
    let new_top = fromIntegral $ (topv - 1) .&. 0x7
    modState $ do
      -- TODO: Update tagWords
      -- Store value at new top
      boundValue (X87_FPUReg (F.mmxReg new_top)) .= v
      -- Update top
      boundValue X87_TopReg .= BVValue knownNat (toInteger new_top)
  x87Pop = do
    topv <- getX87Top
    let new_top = (topv + 1) .&. 0x7
    modState $ do
      -- Update top
      boundValue X87_TopReg .= BVValue knownNat (toInteger new_top)

initGenState :: NonceGenerator (ST st_s) ids
             -> MemSegmentOff 64
                -- ^ Address of initial instruction
             -> RegState X86Reg (Value X86_64 ids)
                -- ^ Initial register state
             -> GenState st_s ids
initGenState nonce_gen addr s =
    GenState { assignIdGen = nonce_gen
             , _blockSeq = BlockSeq { _nextBlockID    = 1
                                    , _frontierBlocks = Seq.empty
                                    }
             , _blockState     = emptyPreBlock s 0 addr
             , genAddr = addr
             }

-- | Describes the reason the translation error occured.
data X86TranslateErrorReason
   = DecodeError (MemoryError 64)
     -- ^ A memory error occured in decoding with Flexdis
   | UnsupportedInstruction F.InstructionInstance
     -- ^ The instruction is not supported by the translator
   | ExecInstructionError F.InstructionInstance Text
     -- ^ An error occured when trying to translate the instruction

-- | Describes an error that occured in translation
data X86TranslateError = X86TranslateError { transErrorAddr :: !(MemSegmentOff 64)
                                           , transErrorReason :: !X86TranslateErrorReason
                                           }

instance Show X86TranslateError where
  show err =
      case transErrorReason err of
        DecodeError me ->
          "Memory error at " ++ addr ++ ": " ++ show me
        UnsupportedInstruction i ->
          "Unsupported instruction at " ++ addr ++ ": " ++ show i
        ExecInstructionError i msg ->
          "Error in interpretting instruction at " ++ addr ++ ": " ++ show i ++ "\n  "
          ++ Text.unpack msg
    where addr = show (transErrorAddr err)

-- | Disassemble block, returning list of blocks read so far, ending PC, and an optional error.
-- and ending PC.
disassembleBlockImpl :: forall st_s ids
                     .  Memory 64
                     -> GenState st_s ids
                     -- ^ State information for disassembling.
                     -> MemSegmentOff 64
                     -- ^ Address to disassemble
                     -> MemWord 64
                         -- ^ Maximum offset for this addr.
                     -> ST st_s (BlockSeq ids, MemWord 64, Maybe X86TranslateError)
disassembleBlockImpl mem gs curIPAddr max_offset = do
  let seg = msegSegment curIPAddr
  let off = msegOffset curIPAddr
  let returnWithError rsn =
        let err = X86TranslateError curIPAddr rsn
            term = (`TranslateError` Text.pack (show err))
            b = finishBlock' (gs^.blockState) term
            res = seq b $ gs^.blockSeq & frontierBlocks %~ (Seq.|> b)
         in return (res, off, Just err)
  case readInstruction mem curIPAddr of
    Left msg -> do
      returnWithError (DecodeError msg)
    Right (i, next_ip_off) -> do
      let next_ip :: MemAddr 64
          next_ip = relativeAddr seg next_ip_off
      let next_ip_val :: BVValue X86_64 ids 64
          next_ip_val = RelocatableValue n64 next_ip

      case execInstruction (ValueExpr next_ip_val) i of
        Nothing -> do
          returnWithError (UnsupportedInstruction i)
        Just exec -> do
          gsr <-
            runExceptT $ runX86Generator (\() s -> pure (mkGenResult s)) gs $ do
              let next_ip_word = fromIntegral $
                    case segmentBase seg of
                      Just base -> base + off
                      Nothing -> off
              let line = show curIPAddr ++ ": " ++ show (F.ppInstruction next_ip_word i)
              addStmt (Comment (Text.pack line))
              exec
          case gsr of
            Left msg -> do
              returnWithError (ExecInstructionError i msg)
            Right res -> do
              case resState res of
                -- If next ip is exactly the next_ip_val then keep running.
                Just p_b
                  | Seq.null (resBlockSeq res ^. frontierBlocks)
                  , v <- p_b^.(pBlockState . curIP)
                  , v == next_ip_val
                    -- Check to see if we should continue
                  , next_ip_off < max_offset
                  , Just next_ip_segaddr <- asSegmentOff mem next_ip -> do
                 let gs2 = GenState { assignIdGen = assignIdGen gs
                                    , _blockSeq = resBlockSeq res
                                    , _blockState = p_b
                                    , genAddr = next_ip_segaddr
                                    }
                 disassembleBlockImpl mem gs2 next_ip_segaddr max_offset
                _ -> do
                  let gs3 = finishBlock FetchAndExecute res
                  return (gs3, next_ip_off, Nothing)

-- | Disassemble block, returning either an error, or a list of blocks
-- and ending PC.
disassembleBlock :: forall s
                 .  Memory 64
                 -> NonceGenerator (ST s) s
                 -> ExploreLoc
                 -> MemWord 64
                    -- ^ Maximum number of bytes in ths block.
                 -> ST s ([Block X86_64 s], MemWord 64, Maybe X86TranslateError)
disassembleBlock mem nonce_gen loc max_size = do
  let addr = loc_ip loc
  let gs = initGenState nonce_gen addr (initX86State loc)
  let sz = msegOffset addr + max_size
  (gs', next_ip_off, maybeError) <- disassembleBlockImpl mem gs addr sz
  assert (next_ip_off > msegOffset addr) $ do
  let block_sz = next_ip_off - msegOffset addr
  pure $ (Fold.toList (gs'^.frontierBlocks), block_sz, maybeError)

-- | The abstract state for a function begining at a given address.
initialX86AbsState :: MemSegmentOff 64 -> AbsBlockState X86Reg
initialX86AbsState addr =
  top & setAbsIP addr
      & absRegState . boundValue sp_reg .~ concreteStackOffset (relativeSegmentAddr addr) 0
        -- x87 top register points to top of stack.
      & absRegState . boundValue X87_TopReg .~ FinSet (Set.singleton 7)
        -- Direction flag is initially zero.
      & absRegState . boundValue DF .~ BoolConst False
      & startAbsStack .~ Map.singleton 0 (StackEntry (BVMemRepr n8 LittleEndian) ReturnAddr)

preserveFreeBSDSyscallReg :: X86Reg tp -> Bool
preserveFreeBSDSyscallReg r
  | Just Refl <- testEquality r CF  = False
  | Just Refl <- testEquality r RAX = False
  | otherwise = True

-- | Linux preserves the same registers the x86_64 ABI does
linuxSystemCallPreservedRegisters :: Set.Set (Some X86Reg)
linuxSystemCallPreservedRegisters = x86CalleeSavedRegs


-- | Transfer some type into an abstract value given a processor state.
transferAbsValue :: AbsProcessorState X86Reg ids
                 -> X86PrimFn (Value X86_64 ids) tp
                 -> AbsValue 64 tp
transferAbsValue r f =
  case f of
    ReadLoc _  -> TopV
    ReadFSBase -> TopV
    ReadGSBase -> TopV
    CPUID _    -> TopV
    RDTSC      -> TopV
    XGetBV _   -> TopV
    PShufb{}   -> TopV
      -- We know only that it will return up to (and including(?)) cnt
    MemCmp _sz cnt _src _dest _rev
      | Just upper <- hasMaximum knownType (transferValue r cnt) ->
          stridedInterval $ SI.mkStridedInterval knownNat False 0 upper 1
      | otherwise -> TopV
    RepnzScas _sz _val _buf cnt
      | Just upper <- hasMaximum knownType (transferValue r cnt) ->
          stridedInterval $ SI.mkStridedInterval knownNat False 0 upper 1
      | otherwise -> TopV
    MMXExtend{}   -> TopV
    X86IDiv{} -> TopV
    X86IRem{} -> TopV
    X86Div{}  -> TopV
    X86Rem{}  -> TopV

-- | Disassemble block, returning either an error, or a list of blocks
-- and ending PC.
tryDisassembleBlockFromAbsState :: forall s
                             .  Memory 64
                             -> NonceGenerator (ST s) s
                             -> MemSegmentOff 64
                             -- ^ Address to disassemble at
                             -> MemWord 64
                             -- ^ Maximum size of this block
                             -> AbsBlockState X86Reg
                             -- ^ Abstract state of processor for defining state.
                             -> ExceptT String (ST s) ([Block X86_64 s], MemWord 64, Maybe String)
tryDisassembleBlockFromAbsState mem nonce_gen addr max_size ab = do
  t <-
    case asConcreteSingleton (ab^.absRegState^.boundValue X87_TopReg) of
      Nothing -> throwError "Could not determine height of X87 stack."
      Just t -> pure t
  d <-
    case asConcreteSingleton (ab^.absRegState^.boundValue DF) of
      Nothing -> do
        throwError $ "Could not determine df flag " ++ show (ab^.absRegState^.boundValue DF)
      Just d -> pure d
  let loc = ExploreLoc { loc_ip = addr
                       , loc_x87_top = fromInteger t
                       , loc_df_flag = d /= 0
                       }
  let gs = initGenState nonce_gen addr (initX86State loc)
  let off = msegOffset  addr
  (gs', next_ip_off, maybeError) <- lift $ disassembleBlockImpl mem gs addr (off + max_size)
  assert (next_ip_off > off) $ do
  let sz = next_ip_off - off
  let blocks = Fold.toList (gs'^.frontierBlocks)
  pure $! (blocks, sz, show <$> maybeError)

-- | Disassemble block, returning either an error, or a list of blocks
-- and ending PC.
disassembleBlockFromAbsState :: forall s
                             .  Memory 64
                             -> NonceGenerator (ST s) s
                             -> MemSegmentOff 64
                             -- ^ Address to disassemble at
                             -> MemWord 64
                             -- ^ Maximum size of this block
                             -> AbsBlockState X86Reg
                             -- ^ Abstract state of processor for defining state.
                             -> ST s ([Block X86_64 s], MemWord 64, Maybe String)
disassembleBlockFromAbsState mem nonce_gen addr max_size ab = do
  mr <- runExceptT $ tryDisassembleBlockFromAbsState mem nonce_gen addr max_size ab
  case mr of
    Left msg -> pure ([], 0, Just msg)
    Right r ->  pure r

-- | Attempt to identify the write to a stack return address, returning
-- instructions prior to that write and return  values.
--
-- This can also return Nothing if the call is not supported.
identifyX86Call :: Memory 64
                -> [Stmt X86_64 ids]
                -> RegState X86Reg (Value X86_64 ids)
                -> Maybe (Seq (Stmt X86_64 ids), MemSegmentOff 64)
identifyX86Call mem stmts0 s = go (Seq.fromList stmts0) Seq.empty
  where -- Get value of stack pointer
        next_sp = s^.boundValue sp_reg
        -- Recurse on statements.
        go stmts after =
          case Seq.viewr stmts of
            Seq.EmptyR -> Nothing
            prev Seq.:> stmt
              -- Check for a call statement by determining if the last statement
              -- writes an executable address to the stack pointer.
              | WriteMem a _repr val <- stmt
              , Just _ <- testEquality a next_sp
                -- Check this is the right length.
              , Just Refl <- testEquality (typeRepr next_sp) (typeRepr val)
                -- Check if value is a valid literal address
              , Just val_a <- asLiteralAddr val
                -- Check if segment of address is marked as executable.
              , Just ret_addr <- asSegmentOff mem val_a
              , segmentFlags (msegSegment ret_addr) `Perm.hasPerm` Perm.execute ->
                Just (prev Seq.>< after, ret_addr)
                -- Stop if we hit any architecture specific instructions prior to
                -- identifying return address since they may have side effects.
              | ExecArchStmt _ <- stmt -> Nothing
                -- Otherwise skip over this instruction.
              | otherwise -> go prev (stmt Seq.<| after)

-- | This is designed to detect returns from the register state representation.
--
-- It pattern matches on a 'RegState' to detect if it read its instruction
-- pointer from an address that stored on the stack pointer.
identifyX86Return :: [Stmt X86_64 ids]
                  -> RegState X86Reg (Value X86_64 ids)
                  -> Maybe [Stmt X86_64 ids]
identifyX86Return stmts s = do
  -- How stack pointer moves when a call is made
  let stack_adj = -8
  let next_ip = s^.boundValue ip_reg
      next_sp = s^.boundValue sp_reg
  case next_ip of
    AssignedValue (Assignment _ (ReadMem ip_addr _))
      | let (ip_base, ip_off) = asBaseOffset ip_addr
      , let (sp_base, sp_off) = asBaseOffset next_sp
      , (ip_base, ip_off) == (sp_base, sp_off + stack_adj) ->
        let isRetLoad stmt =
              case stmt of
                AssignStmt asgn
                  | Just Refl <- testEquality (assignId asgn) (assignId  asgn) -> True
                _ -> False
         in Just $ filter (not . isRetLoad) stmts
    _ -> Nothing

-- | Return state post call
x86PostCallAbsState :: AbsBlockState X86Reg
                    -> MemSegmentOff 64
                    -> AbsBlockState X86Reg
x86PostCallAbsState =
  let params = CallParams { postCallStackDelta = 8
                          , preserveReg = \r -> Set.member (Some r) x86CalleeSavedRegs
                          }
   in absEvalCall params

freeBSD_syscallPersonality :: SyscallPersonality X86_64
freeBSD_syscallPersonality =
  SyscallPersonality { spTypeInfo = FreeBSD.syscallInfo
                     , spResultRegisters = [ Some RAX ]
                     }


addValueListDemands :: [Some (Value arch ids)] -> DemandComp arch ids ()
addValueListDemands = mapM_ (viewSome addValueDemands)

x86DemandContext :: DemandContext X86_64 ids
x86DemandContext =
  DemandContext { addArchStmtDemands = addValueListDemands . valuesInX86Stmt
                , addArchFnDemands   = addValueListDemands . foldMapFC (\v -> [Some v])
                , archFnHasSideEffects = x86PrimFnHasSideEffects
                }

-- | Common architecture information for X86_64
x86_64_info :: (forall tp . X86Reg tp -> Bool)
               -- ^ Function that returns true if we should preserve a register across a system call.
            -> ArchitectureInfo X86_64
x86_64_info preservePred =
  ArchitectureInfo { withArchConstraints = \x -> x
                   , archAddrWidth      = Addr64
                   , archEndianness     = LittleEndian
                   , jumpTableEntrySize = 8
                   , disassembleFn      = disassembleBlockFromAbsState
                   , preserveRegAcrossSyscall = preservePred
                   , mkInitialAbsState = \_ -> initialX86AbsState
                   , absEvalArchFn     = transferAbsValue
                   , absEvalArchStmt   = \s _ -> s
                   , postCallAbsState = x86PostCallAbsState
                   , identifyCall      = identifyX86Call
                   , identifyReturn    = identifyX86Return
                   , rewriteArchFn     = rewriteX86PrimFn
                   , rewriteArchStmt   = rewriteX86Stmt
                   , rewriteArchTermStmt = rewriteX86TermStmt
                   , archDemandContext = x86DemandContext
                   }

-- | Architecture information for X86_64 on FreeBSD.
x86_64_freeBSD_info :: ArchitectureInfo X86_64
x86_64_freeBSD_info = x86_64_info preserveFreeBSDSyscallReg

linux_syscallPersonality :: SyscallPersonality X86_64
linux_syscallPersonality =
  SyscallPersonality { spTypeInfo = Linux.syscallInfo
                     , spResultRegisters = [Some RAX]
                     }

-- | Architecture information for X86_64.
x86_64_linux_info :: ArchitectureInfo X86_64
x86_64_linux_info = x86_64_info preserveReg
  where preserveReg r = Set.member (Some r) linuxSystemCallPreservedRegisters
