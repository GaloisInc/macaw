{-
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# OPTIONS_GHC -Wwarn #-}
module Data.Macaw.Symbolic.App where

import           Control.Monad.Identity
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Types as M
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Types as C

type family ToCrucibleType (mtp :: M.Type) :: C.CrucibleType where
  ToCrucibleType (M.BVType w) = C.BVType w

type CrucGen = Identity

valueToCrucible :: M.Value arch ids tp -> CrucGen (C.Value s (ToCrucibleType tp))
valueToCrucible = undefined

valueToBool :: M.Value arch ids M.BoolType -> CrucGen (C.Value s C.BoolType)
valueToBool = undefined

crucibleValue :: C.App (C.Value s) ctp -> CrucGen (C.Value s ctp)
crucibleValue = undefined

appToCrucible :: M.App (M.Value arch ids) tp -> CrucGen (C.Value s (ToCrucibleType tp))
appToCrucible app =
  case app of
    M.Mux w c t f -> do
      crucibleValue =<<
        C.BVIte <$> valueToBool c
                <*> pure w
                <*> valueToCrucible t
                <*> valueToCrucible f
