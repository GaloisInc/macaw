{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

module Utils
  ( withSym
  , mkPtr
  ) where

import qualified Data.BitVector.Sized as BV
import           Data.Word (Word64)
import           Numeric.Natural (Natural)

import qualified Data.Macaw.CFG as MC
import qualified Lang.Crucible.LLVM.MemModel as CL
import qualified Lang.Crucible.LLVM.MemModel.Pointer as CLP
import           Data.Parameterized.Nonce (newIONonceGenerator)
import           Data.Parameterized.Some (Some(..))
import qualified What4.Expr as WE
import qualified What4.Expr.Builder as WEB
import qualified What4.Interface as WI

-- | Set up a What4 expression builder for tests.
withSym :: (forall t. WEB.ExprBuilder t WE.EmptyExprBuilderState (WEB.Flags WEB.FloatIEEE) -> IO a) -> IO a
withSym f = do
  Some ng <- newIONonceGenerator
  sym <- WEB.newExprBuilder WEB.FloatIEEERepr WE.EmptyExprBuilderState ng
  f sym

-- | Build an LLVMPointer from a concrete block number and offset.
mkPtr ::
  WI.IsExprBuilder sym =>
  sym ->
  MC.AddrWidthRepr w ->
  Natural ->
  Word64 ->
  IO (CL.LLVMPtr sym w)
mkPtr sym repr blk off = do
  blkSym <- WI.natLit sym blk
  offSym <- case repr of
    MC.Addr32 -> WI.bvLit sym (WI.knownNat @32)
                   (BV.mkBV (WI.knownNat @32) (fromIntegral @Word64 @Integer off))
    MC.Addr64 -> WI.bvLit sym (WI.knownNat @64) (BV.word64 off)
  pure (CLP.LLVMPointer blkSym offSym)
