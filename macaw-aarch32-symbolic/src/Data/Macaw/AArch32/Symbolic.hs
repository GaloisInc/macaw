{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.AArch32.Symbolic (

  ) where

import           Data.Kind ( Type )
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Backend as MSB
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import qualified SemMC.Architecture.AArch32 as SA

import qualified Lang.Crucible.CFG.Extension as CE
import qualified Lang.Crucible.Types as CT

instance MS.ArchInfo SA.AArch32 where
  archVals _ = Nothing

data AArch32StmtExtension (f :: CT.CrucibleType -> Type) (ctp :: CT.CrucibleType) where

instance FC.FunctorFC AArch32StmtExtension where
instance FC.FoldableFC AArch32StmtExtension where
instance FC.TraversableFC AArch32StmtExtension where
instance CE.TypeApp AArch32StmtExtension where
instance CE.PrettyApp AArch32StmtExtension where

type instance MSB.MacawArchStmtExtension SA.AArch32 =
  AArch32StmtExtension

-- Dummy register context
--
-- For now, just add one register
type RegContext = Ctx.EmptyCtx Ctx.::> MT.BVType 32
type instance MS.ArchRegContext SA.AArch32 = RegContext
