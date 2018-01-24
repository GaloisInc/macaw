{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language KindSignatures #-}
{-# Language DataKinds #-}
module Data.Macaw.X86.Semantics where

import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Solver.Interface as C
import qualified Lang.Crucible.Types as C

import qualified Data.Macaw.Types as M
import           Data.Macaw.Symbolic.CrucGen(MacawExt)
import           Data.Macaw.Symbolic
import qualified Data.Macaw.X86 as M


type S sym rtp bs r ctx =
  C.CrucibleState MacawSimulatorState sym (MacawExt M.X86_64) rtp bs r ctx

semantics ::
  (C.IsSymInterface sym, ToCrucibleType mt ~ t) =>
  M.X86PrimFn (AtomWrapper (C.RegEntry sym)) mt ->
  S sym rtp bs r ctx -> IO (C.RegValue sym t, S sym rtp bs r ctx)
semantics _x _s = undefined



--------------------------------------------------------------------------------

newtype AtomWrapper (f :: C.CrucibleType -> *) (tp :: M.Type)
  = AtomWrapper (f (ToCrucibleType tp))

liftAtomMap :: (forall s. f s -> g s) -> AtomWrapper f t -> AtomWrapper g t
liftAtomMap f (AtomWrapper x) = AtomWrapper (f x)

liftAtomTrav ::
  Applicative m =>
  (forall s. f s -> m (g s)) -> (AtomWrapper f t -> m (AtomWrapper g t))
liftAtomTrav f (AtomWrapper x) = AtomWrapper <$> f x

liftAtomIn :: (forall s. f s -> a) -> AtomWrapper f t -> a
liftAtomIn f (AtomWrapper x) = f x



