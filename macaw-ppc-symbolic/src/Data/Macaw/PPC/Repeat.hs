{-# LANGUAGE DataKinds #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.PPC.Symbolic.Repeat (
  CtxRepeat,
  RepeatAssign(..)
  ) where

import           GHC.TypeLits
import qualified Data.Parameterized.Context as Ctx

type family CtxRepeat (n :: Nat) (c :: k) :: Ctx.Ctx k where
  CtxRepeat 0 c = Ctx.EmptyCtx
  CtxRepeat n c = CtxRepeat (n - 1) c Ctx.::> c

class RepeatAssign (tp :: k) (ctx :: Ctx.Ctx k) where
  repeatAssign :: (Int -> f tp) -> Ctx.Assignment f ctx

instance RepeatAssign tp Ctx.EmptyCtx where
  repeatAssign _ = Ctx.Empty

instance RepeatAssign tp ctx => RepeatAssign tp (ctx Ctx.::> tp) where
  repeatAssign f =
    repeatAssign f Ctx.:> f (Ctx.sizeInt (Ctx.size r))
