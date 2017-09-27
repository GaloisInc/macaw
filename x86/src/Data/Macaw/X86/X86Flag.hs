{-
Copyright        : (c) Galois, Inc 2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This contains a type for modeling the X86 flags
-}
{-# LANGUAGE PatternSynonyms #-}
module Data.Macaw.X86.X86Flag
  ( X86Flag
  , flagIndex
  , pattern CF
  , pattern PF
  , pattern AF
  , pattern ZF
  , pattern SF
  , pattern TF
  , pattern IF
  , pattern DF
  , pattern OF
  , flagList
  ) where

import qualified Data.Vector as V
import           Data.Word

-- | X86 flag
newtype X86Flag = X86Flag { flagIndex :: Word8 }
  deriving (Eq, Ord)

flagNames :: V.Vector String
flagNames = V.fromList
  [ "cf", "RESERVED", "pf", "RESERVED", "af", "RESERVED"
  , "zf", "sf",       "tf", "if",       "df", "of"
  , "iopl", "nt", "SBZ", "rf", "vm", "ac", "vif", "vip", "id"
  ]

instance Show X86Flag where
  show (X86Flag i) =
    case flagNames V.!? fromIntegral i of
      Just nm -> nm
      Nothing -> "Unknown" ++ show i

pattern CF :: X86Flag
pattern CF = X86Flag 0

pattern PF :: X86Flag
pattern PF = X86Flag 2

pattern AF :: X86Flag
pattern AF = X86Flag 4

pattern ZF :: X86Flag
pattern ZF = X86Flag 6

pattern SF :: X86Flag
pattern SF = X86Flag 7

pattern TF :: X86Flag
pattern TF = X86Flag 8

pattern IF :: X86Flag
pattern IF = X86Flag 9

pattern DF :: X86Flag
pattern DF = X86Flag 10

pattern OF :: X86Flag
pattern OF = X86Flag 11

-- | Return list of x86 flags
flagList :: [X86Flag]
flagList = X86Flag <$> [0,2,4,6,7,8,9,10,11]
