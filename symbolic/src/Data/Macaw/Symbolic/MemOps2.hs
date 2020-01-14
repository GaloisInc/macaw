{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE LambdaCase #-}
module Data.Macaw.Symbolic.MemOps2 where

import           Control.Applicative
import           Control.Monad.State
import           Data.List
import qualified Data.Vector as V
import           GHC.TypeNats (type (<=))
import           Numeric

import Data.Macaw.CFG.AssignRhs (MemRepr(..))
import Data.Macaw.Memory (AddrWidthRepr(..), Endianness, addrWidthNatRepr)
import Data.Macaw.Symbolic.PersistentState (ToCrucibleType)
import Lang.Crucible.Backend (IsSymInterface)
import Lang.Crucible.LLVM.MemModel (LLVMPtr, pattern LLVMPointer, llvmPointer_bv)
import Lang.Crucible.Simulator.RegValue (RegValue)
import Lang.Crucible.Types (BoolType)
import What4.Concrete (ConcreteVal(..))
import What4.Interface -- (NatRepr, knownRepr, BaseTypeRepr(..), SolverSymbol, userSymbol, freshConstant, natLit)

data MemOpCondition sym
  = Unconditional
  | Conditional (Pred sym)

deriving instance Show (Pred sym) => Show (MemOpCondition sym)

data MemOpDirection = Read | Write deriving (Bounded, Enum, Eq, Ord, Read, Show)

data MemOp sym ptrW where
  MemOp ::
    { moAddr :: LLVMPtr sym ptrW
    , moDir :: MemOpDirection
    , moCond :: MemOpCondition sym
    , moSize :: NatRepr w
    , moVal :: LLVMPtr sym w
    , moEnd :: Endianness
    } -> MemOp sym ptrW

type MemImpl2 sym ptrW = [MemOp sym ptrW]

doReadMem ::
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemImpl2 sym ptrW) IO (RegValue sym (ToCrucibleType ty))
doReadMem sym ptrWidth ptr memRepr = do
  val <- liftIO $ freshRegValue sym ptr memRepr
  doMemOpInternal sym Read Unconditional ptrWidth ptr val memRepr
  pure val

doCondReadMem ::
  IsSymInterface sym =>
  sym ->
  RegValue sym BoolType ->
  RegValue sym (ToCrucibleType ty) ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  StateT (MemImpl2 sym ptrW) IO (RegValue sym (ToCrucibleType ty))
doCondReadMem sym cond def ptrWidth ptr memRepr = do
  val <- liftIO $ freshRegValue sym ptr memRepr
  doMemOpInternal sym Read (Conditional cond) ptrWidth ptr val memRepr
  liftIO $ iteDeep sym cond val def memRepr

doWriteMem ::
  IsSymInterface sym =>
  sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemImpl2 sym ptrW) IO ()
doWriteMem sym = doMemOpInternal sym Write Unconditional

doCondWriteMem ::
  IsSymInterface sym =>
  sym ->
  RegValue sym BoolType ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemImpl2 sym ptrW) IO ()
doCondWriteMem sym cond = doMemOpInternal sym Write (Conditional cond)

freshRegValue :: forall sym ptrW ty.
  IsSymInterface sym =>
  sym ->
  LLVMPtr sym ptrW ->
  MemRepr ty ->
  IO (RegValue sym (ToCrucibleType ty))
freshRegValue sym (LLVMPointer reg off) = go 0 where
  go :: Integer -> MemRepr ty' -> IO (RegValue sym (ToCrucibleType ty'))
  go n (BVMemRepr byteWidth _endianness) = do
    let bitWidth = natMultiply (knownNat @8) byteWidth
    symbolContent <- ioSolverSymbol . intercalate "_" $ describe byteWidth n
    content <- multiplicationIsMonotonic @8 bitWidth $ freshConstant sym symbolContent (BaseBVRepr bitWidth)
    llvmPointer_bv sym content

  go _n (FloatMemRepr _infoRepr _endianness) = fail "creating fresh float values not supported in freshRegValue"

  go n (PackedVecMemRepr countRepr recRepr) = V.generateM (fromInteger (intValue countRepr)) $ \i ->
    go (n + memReprByteSize recRepr * fromIntegral i) recRepr

  describe :: NatRepr w -> Integer -> [String]
  describe = case (asConcrete reg, asConcrete off) of
    (Just (ConcreteNat regVal), Just (ConcreteBV _ offVal)) -> \byteWidth n ->
      ["read", show (natValue byteWidth), show regVal, "0x" ++ showHex (offVal + n) ""]
    _ -> \byteWidth _n -> ["read", show (natValue byteWidth), "symbolic_location"]

doMemOpInternal :: forall sym ptrW ty.
  IsSymInterface sym =>
  sym ->
  MemOpDirection ->
  MemOpCondition sym ->
  AddrWidthRepr ptrW ->
  LLVMPtr sym ptrW ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  StateT (MemImpl2 sym ptrW) IO ()
doMemOpInternal sym dir cond ptrWidth = go where
  go :: LLVMPtr sym ptrW -> RegValue sym (ToCrucibleType ty') -> MemRepr ty' -> StateT (MemImpl2 sym ptrW) IO ()
  go ptr@(LLVMPointer reg off) regVal = \case
    BVMemRepr byteWidth endianness -> logOp MemOp
      { moAddr = ptr
      , moDir = dir
      , moCond = cond
      , moSize = natMultiply (knownNat @8) byteWidth
      , moVal = regVal
      , moEnd = endianness
      }
    FloatMemRepr _infoRepr _endianness -> fail "reading floats not supported in doMemOpInternal"
    PackedVecMemRepr _countRepr recRepr -> addrWidthsArePositive ptrWidth $ do
      elemSize <- liftIO $ bvLit sym ptrWidthNatRepr (memReprByteSize recRepr)
      flip V.imapM_ regVal $ \i recRegVal -> do
        off' <- liftIO $ do
          symbolicI <- bvLit sym ptrWidthNatRepr (toInteger i)
          dOff <- bvMul sym symbolicI elemSize
          bvAdd sym off dOff
        go (LLVMPointer reg off') recRegVal recRepr

  ptrWidthNatRepr = addrWidthNatRepr ptrWidth

iteDeep ::
  IsSymInterface sym =>
  sym ->
  Pred sym ->
  RegValue sym (ToCrucibleType ty) ->
  RegValue sym (ToCrucibleType ty) ->
  MemRepr ty ->
  IO (RegValue sym (ToCrucibleType ty))
iteDeep sym cond t f = \case
  BVMemRepr byteWidth _endianness -> let
    bitWidth = natMultiply (knownNat @8) byteWidth
    LLVMPointer treg toff = t
    LLVMPointer freg foff = f
    in multiplicationIsMonotonic @8 bitWidth
    $ liftA2 LLVMPointer (natIte sym cond treg freg) (bvIte sym cond toff foff)
  FloatMemRepr _infoRepr _endianness -> fail "ite on floats not supported in iteDeep"
  PackedVecMemRepr countRepr recRepr -> V.generateM (fromInteger (intValue countRepr)) $ \i ->
    iteDeep sym cond (t V.! i) (f V.! i) recRepr

logOp :: (MonadState (MemImpl2 sym ptrW) m) => MemOp sym ptrW -> m ()
logOp op = modify (op:)

addrWidthsArePositive :: AddrWidthRepr w -> (1 <= w => a) -> a
addrWidthsArePositive Addr32 a = a
addrWidthsArePositive Addr64 a = a

multiplicationIsMonotonic :: forall x w a. (1 <= x, 1 <= w) => NatRepr (x*w) -> (1 <= x*w => a) -> a
multiplicationIsMonotonic xw a = case compareNat (knownNat @0) xw of
  NatLT _ -> a
  _ -> error $ "The impossible happened: 1 <= x and 1 <= w, but x*w = " ++ show (natValue xw) ++ " and 1 > x*w"

memReprByteSize :: MemRepr ty -> Integer
memReprByteSize (BVMemRepr byteWidth _) = intValue byteWidth
memReprByteSize (FloatMemRepr _ _) = error "byte size of floats not supported in memReprByteSize"
memReprByteSize (PackedVecMemRepr countRepr recRepr) = intValue countRepr * memReprByteSize recRepr

ioSolverSymbol :: String -> IO SolverSymbol
ioSolverSymbol = either (fail . show) pure . userSymbol
