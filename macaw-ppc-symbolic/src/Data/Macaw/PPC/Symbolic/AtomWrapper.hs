{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
module Data.Macaw.PPC.Symbolic.AtomWrapper (
  AtomWrapper(..),
  liftAtomMap,
  liftAtomTrav,
  liftAtomIn
  ) where

import qualified Data.Kind as DK
import qualified Lang.Crucible.Types as C
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS

newtype AtomWrapper (f :: C.CrucibleType -> DK.Type) (tp :: MT.Type)
  = AtomWrapper (f (MS.ToCrucibleType tp))

liftAtomMap :: (forall s. f s -> g s) -> AtomWrapper f t -> AtomWrapper g t
liftAtomMap f (AtomWrapper x) = AtomWrapper (f x)

liftAtomTrav ::
  Functor m =>
  (forall s. f s -> m (g s)) -> (AtomWrapper f t -> m (AtomWrapper g t))
liftAtomTrav f (AtomWrapper x) = AtomWrapper <$> f x

liftAtomIn :: (forall s. f s -> a) -> AtomWrapper f t -> a
liftAtomIn f (AtomWrapper x) = f x


