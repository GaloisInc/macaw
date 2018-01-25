{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language KindSignatures #-}
{-# Language DataKinds #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language EmptyCase #-}
{-# Language ScopedTypeVariables #-}
{-# Language TypeOperators #-}
module Data.Macaw.X86.Semantics where

import Data.Parameterized.NatRepr
import Data.Bits(shiftR, (.&.))
import Data.Word(Word8)
import GHC.TypeLits(KnownNat)

import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.RegMap
import qualified Lang.Crucible.Simulator.Evaluation as C
import           Lang.Crucible.Syntax
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.Solver.Interface hiding (IsExpr)
import           Lang.Crucible.Types
import qualified Lang.Crucible.Vector as V
import           Lang.Crucible.Utils.Endian(Endian(..))

import qualified Data.Macaw.Types as M
import           Data.Macaw.Symbolic.CrucGen(MacawExt)
import           Data.Macaw.Symbolic
import qualified Data.Macaw.X86 as M
import qualified Data.Macaw.X86.ArchTypes as M


type S sym rtp bs r ctx =
  CrucibleState MacawSimulatorState sym (MacawExt M.X86_64) rtp bs r ctx

semantics ::
  (IsSymInterface sym, ToCrucibleType mt ~ t) =>
  M.X86PrimFn (AtomWrapper (RegEntry sym)) mt ->
  S sym rtp bs r ctx -> IO (RegValue sym t, S sym rtp bs r ctx)
semantics x s = do v <- pureSem (stateSymInterface s) x
                   return (v,s)

-- | Semantics for operations that do not affect Crucible's state directly.
pureSem :: (IsSymInterface sym) =>
  sym {- ^ Handle to the simulator -} ->
  M.X86PrimFn (AtomWrapper (RegEntry sym)) mt {- ^ Instruction -} ->
  IO (RegValue sym (ToCrucibleType mt)) -- ^ Resulting value
pureSem sym fn =
  case fn of

    M.VOp1 w op1 x ->
      case op1 of
        M.VShiftL n ->
           unpack BigEndian w n8 x $ \vecIn ->
           pack BigEndian sym (V.shiftL (fromIntegral n) zero vecIn)

        M.VShufD mask ->
           unpack LittleEndian w n32 x $ \vecIn ->
           pack LittleEndian sym (shuffle mask vecIn)

{-
    M.VOp2 w op2 x y ->
      case op2 of
        M.VPOr          -> evalE sym $ app $ BVOr  w (getVal x) (getVal y)
        M.VPXor         -> evalE sym $ app $ BVXor w (getVal x) (getVal y)
        M.VPAlignR i    ->
          case testEquality w n128 of
            Just Refl ->
              unpack BigEndian w n8 x $ \xs ->
              unpack BigEndian w n8 y $ \ys ->
              pack BigEndian sym (vpalign i xs ys)

        M.VPShufB       -> undefined
        M.VAESEnc       -> undefined
        M.VAESEncLast   -> undefined
        M.VPCLMULQDQ i  -> undefined
-}

-- | Assumes big-endian split
vpalign :: Word8 ->
           V.Vector 16 (E sym (BVType 8)) ->
           V.Vector 16 (E sym (BVType 8)) ->
           V.Vector 16 (E sym (BVType 8))
vpalign i xs ys =
  V.slice n0 n16 (V.shiftR (fromIntegral i) zero (V.append xs ys))

-- | Shuffling with a mask.
-- For more info, see `VPSHUFD` Intel instruction.
shuffle :: Word8 -> V.Vector n a -> V.Vector n a
shuffle w = V.shuffle getField
  where
  -- Every 2 bits correspond to an index in the input.
  -- The 4 fields packed in the 8 bit input mask are repeated.
  getField x = let (d',r') = divMod x 4
                   d = fromIntegral d'
                   r = fromIntegral r'
               in 4 * d + fromIntegral ((w `shiftR` (2 * r)) .&. 0x03)



-- | Package-up a vector expression to a bit-vector, and evaluate it.
pack :: (IsSymInterface sym, KnownNat w, 1 <= w) =>
  Endian -> sym ->
  V.Vector n (E sym (BVType w)) -> IO (RegValue sym (BVType (n*w)))
pack e sym xs = evalE sym (V.toBV e knownNat xs)


-- | Split up a bit-vector into a vector.
-- Even though X86 is little endian for memory accesses, this function
-- is parameterized by endianness, as some instructions are more naturally
-- expressed by splitting big-endian-wise (e.g., shifts)
unpack ::
  (1 <= c) =>
  Endian ->
  NatRepr w                               {- ^ Original length -} ->
  NatRepr c                               {- ^ Size of each chunk -} ->
  AtomWrapper (RegEntry sym) (M.BVType w) {- ^ Input value -} ->
  (forall n. (1 <= n, (n * c) ~ w) => V.Vector n (E sym (BVType c)) -> IO a) ->
  IO a
unpack e w c v k =
  withDivModNat w c $ \n r ->
    case testEquality r n0 of
      Just Refl ->
        case testLeq n1 n of
          Just LeqProof -> k (V.fromBV e n c (getVal v))
          _             -> fail "Unexpected 0 size"
      _ -> fail ("Value not a multiple of " ++ show (widthVal c))



getVal :: AtomWrapper (RegEntry sym) mt -> E sym (ToCrucibleType mt)
getVal (AtomWrapper x) = Val x


--------------------------------------------------------------------------------


--------------------------------------------------------------------------------
-- A small functor that allows mixing of values and Crucible expressions.

evalE :: IsSymInterface sym => sym -> E sym t -> IO (RegValue sym t)
evalE sym e = case e of
                Val x  -> return (regValue x)
                Expr a -> evalApp sym a

evalApp :: forall sym t.  IsSymInterface sym =>
         sym -> App () (E sym) t -> IO (RegValue sym t)
evalApp sym = C.evalApp sym intrinsics logger evalExt (evalE sym)
  where
  intrinsics = undefined
  logger _ _ = return ()
  evalExt :: fun -> EmptyExprExtension f a -> IO (RegValue sym a)
  evalExt _ x  = case x of {}

data E :: * -> CrucibleType -> * where
  Val  :: RegEntry sym t -> E sym t
  Expr :: App () (E sym) t -> E sym t

instance IsExpr (E sym) where
  type ExprExt (E sym) = ()
  app = Expr
  asApp e = case e of
              Expr a -> Just a
              _      -> Nothing
  exprType e = case e of
                Expr a -> appType a
                Val r  -> regType r


zero :: (KnownNat w, 1 <= w) => E sym (BVType w)
zero = app (BVLit knownNat 0)

--------------------------------------------------------------------------------

n0 :: NatRepr 0
n0 = knownNat

n1 :: NatRepr 1
n1 = knownNat

n8 :: NatRepr 8
n8 = knownNat

n16 :: NatRepr 16
n16 = knownNat

n32 :: NatRepr 32
n32 = knownNat

n128 :: NatRepr 128
n128 = knownNat

--------------------------------------------------------------------------------

newtype AtomWrapper (f :: CrucibleType -> *) (tp :: M.Type)
  = AtomWrapper (f (ToCrucibleType tp))

liftAtomMap :: (forall s. f s -> g s) -> AtomWrapper f t -> AtomWrapper g t
liftAtomMap f (AtomWrapper x) = AtomWrapper (f x)

liftAtomTrav ::
  Functor m =>
  (forall s. f s -> m (g s)) -> (AtomWrapper f t -> m (AtomWrapper g t))
liftAtomTrav f (AtomWrapper x) = AtomWrapper <$> f x

liftAtomIn :: (forall s. f s -> a) -> AtomWrapper f t -> a
liftAtomIn f (AtomWrapper x) = f x



