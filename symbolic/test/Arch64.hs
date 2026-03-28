{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE InstanceSigs #-}
{-# LANGUAGE TypeFamilies #-}

-- | A minimal phantom 64-bit architecture for testing.
--
-- This provides just enough type family instances to satisfy
-- 'MacawArchConstraints', allowing us to use 'MacawExt Arch64'
-- in tests without depending on a real architecture package.
module Arch64 (Arch64) where

import           Data.Kind (Type)
import           Prettyprinter (Doc)

import qualified Data.Parameterized.TraversableFC as TFC

import qualified Data.Macaw.CFG as MC
import           Data.Macaw.CFG.Core (PrettyF(..))
import qualified Data.Macaw.Types as MT
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.Types as C

import qualified Data.Macaw.Symbolic.Backend as SB

-- | Phantom architecture with 64-bit addresses.
data Arch64

-- | Empty register type (no registers).
data Reg64 (tp :: MT.Type)

type instance MC.ArchReg Arch64 = Reg64
type instance MC.RegAddrWidth Reg64 = 64

-- | Empty architecture-specific statement extension.
data ArchStmt64 (f :: C.CrucibleType -> Type) (tp :: C.CrucibleType)

type instance SB.MacawArchStmtExtension Arch64 = ArchStmt64

-- Trivial instances for empty types

instance PrettyF Reg64 where
  prettyF :: Reg64 tp -> Doc ann
  prettyF = \case {}

instance TFC.TraversableFC ArchStmt64 where
  traverseFC _ = \case {}

instance TFC.FoldableFC ArchStmt64 where
  foldMapFC _ = \case {}

instance TFC.FunctorFC ArchStmt64 where
  fmapFC _ = \case {}

instance C.TypeApp ArchStmt64 where
  appType = \case {}

instance C.PrettyApp ArchStmt64 where
  ppApp _ = \case {}
