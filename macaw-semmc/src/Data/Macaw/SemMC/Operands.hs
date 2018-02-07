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

import           Data.Int ( Int8, Int16 )
import qualified Data.Int.Indexed as I
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.SemMC.Generator as G
import           Data.Macaw.Types
import           Data.Parameterized.NatRepr as NR
import           Data.Word ( Word8, Word16, Word32 )
import qualified Data.Word.Indexed as W
import           GHC.TypeLits

class ExtractValue arch a tp | arch a -> tp where
  extractValue :: a -> G.Generator arch ids s (MC.Value arch ids tp)

class ToRegister a r tp | a r -> tp where
  toRegister :: a -> r tp

instance (KnownNat n, 1 <= n) => ExtractValue arch (W.W n) (BVType n) where
  extractValue w = return $ MC.BVValue NR.knownNat (toIntegerWord (W.unW w))

instance (KnownNat n, 1 <= n) => ExtractValue arch (I.I n) (BVType n) where
  extractValue (I.I i) = return $ MC.BVValue NR.knownNat (toIntegerWord i)

instance ExtractValue arch Bool BoolType where
  extractValue = return . MC.BoolValue

instance ExtractValue arch Int8 (BVType 8) where
  extractValue i = return $ MC.BVValue NR.knownNat (toIntegerWord i)

instance ExtractValue arch Int16 (BVType 16) where
  extractValue i = return $ MC.BVValue NR.knownNat (toIntegerWord i)


-- | Convert to a positive integer through a word type
--
-- We convert through a word because the integer returned is not allowed to be
-- negative.  Negative values must be converted to an unsigned word form, which
-- we can then promote to Integer.
--
-- For current architectures, Word32 is large enough to accommodate
-- all literal values
toIntegerWord :: (Integral a) => a -> Integer
toIntegerWord i = toInteger w
  where
    w :: Word32
    w = fromIntegral i
