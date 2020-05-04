{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}

module Data.Macaw.SemMC.Operands (
  ExtractValue(..),
  ToRegister(..)
  ) where

import qualified Data.BitVector.Sized as BV
import           Data.Int ( Int8, Int16 )
import qualified Data.Int.Indexed as I
import qualified Data.Macaw.CFG.Core as MC
import           Data.Macaw.Types
import           Data.Parameterized.NatRepr as NR
import qualified Data.Word.Indexed as W

class ExtractValue arch a tp | arch a -> tp where
  extractValue :: MC.RegState (MC.ArchReg arch) (MC.Value arch ids) -> a -> MC.Value arch ids tp

class ToRegister a r tp | a r -> tp where
  toRegister :: a -> r tp

instance (KnownNat n, 1 <= n) => ExtractValue arch (W.W n) (BVType n) where
  extractValue _ w = MC.BVValue NR.knownNat (toBV (W.unW w))

instance (KnownNat n, 1 <= n) => ExtractValue arch (I.I n) (BVType n) where
  extractValue _ (I.I i) = MC.BVValue NR.knownNat (toBV i)

instance ExtractValue arch Bool BoolType where
  extractValue _ = MC.BoolValue

instance ExtractValue arch Int8 (BVType 8) where
  extractValue _ i = MC.BVValue NR.knownNat (toBV i)

instance ExtractValue arch Int16 (BVType 16) where
  extractValue _ i = MC.BVValue NR.knownNat (toBV i)


-- | Convert to a bitvector
toBV :: (Integral a, KnownNat w) => a -> BV.BV w
toBV i = BV.mkBV NR.knownNat (toInteger i)
