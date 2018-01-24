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

import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.RegMap
import qualified Lang.Crucible.Simulator.Evaluation as C
import           Lang.Crucible.Syntax
import           Lang.Crucible.CFG.Expr
import           Lang.Crucible.Solver.Interface hiding (IsExpr)
import           Lang.Crucible.Types
import qualified Lang.Crucible.Vector as V
import           Lang.Crucible.Utils.Endian(Endian(LittleEndian))

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

-- | Semantics for operations that does not affect Crucible's state directly.
pureSem :: (IsSymInterface sym) =>
  sym {- ^ Handle to the simulator -} ->
  M.X86PrimFn (AtomWrapper (RegEntry sym)) mt {- ^ Instruction -} ->
  IO (RegValue sym (ToCrucibleType mt)) -- ^ Resulting value
pureSem sym fn =
  case fn of
    M.VOp1 w op1 x ->
      chunksOf n8 w $ \bytes ->
        do let v = getVal x
           case op1 of
             M.VShiftL n ->
                do let vecIn  = V.fromBV bytes n8 v
                       vecOut = V.shiftL (fromIntegral n) (zero n8) vecIn
                   evalE sym (V.toBV LittleEndian n8 vecOut)

             M.VShufD _n -> undefined


chunksOf :: NatRepr c -> NatRepr w ->
           (forall n. (1 <= n, (n * c) ~ w) => NatRepr n -> IO a) -> IO a
chunksOf c w k =
  withDivModNat w c $ \n r ->
    case testEquality r n0 of
      Just Refl ->
        case testLeq n1 n of
          Just LeqProof -> k n
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

n0 :: NatRepr 0
n0 = knownNat

n1 :: NatRepr 1
n1 = knownNat

n8 :: NatRepr 8
n8 = knownNat

zero :: (1 <= w) => NatRepr w -> E sym (BVType w)
zero w = app (BVLit w 0)

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



