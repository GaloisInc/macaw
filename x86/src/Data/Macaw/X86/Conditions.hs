{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the semantics of the different condition code.
-}
{-# LANGUAGE RankNTypes #-}
module Data.Macaw.X86.Conditions
  ( ConditionalDef(..)
  , conditionalDefs
  ) where

import Data.Macaw.Types (BoolType)

import Data.Macaw.X86.Monad

-- Constants for defining semantics of different condition flags.
cond_a, cond_ae, cond_b, cond_be, cond_g, cond_ge, cond_l, cond_le, cond_o, cond_p, cond_s, cond_z,
  cond_no, cond_np, cond_ns, cond_nz :: Semantics m => m (Value m BoolType)

cond_a = (\c z -> boolAnd (boolNot c) (boolNot z)) <$> get cf_loc <*> get zf_loc
cond_ae  = boolNot <$> get cf_loc
cond_b   = get cf_loc
cond_be  = boolOr <$> get cf_loc <*> get zf_loc
cond_g   = (\z s o -> boolAnd (boolNot z) (boolEq s o)) <$> get zf_loc <*> get sf_loc <*> get of_loc
cond_le  = (\z s o -> boolOr z (boolXor s o)) <$> get zf_loc <*> get sf_loc <*> get of_loc
cond_ge  = (\s o   -> boolEq s o)     <$> get sf_loc <*> get of_loc
cond_l   = (\s o   -> boolXor s o) <$> get sf_loc <*> get of_loc
cond_o   = get of_loc
cond_p   = get pf_loc
cond_s   = get sf_loc
cond_z   = get zf_loc
cond_no  = boolNot <$> cond_o
cond_np  = boolNot <$> cond_p
cond_ns  = boolNot <$> cond_s
cond_nz  = boolNot <$> cond_z

newtype ConditionalDef = ConditionalDef (forall m . Semantics m => m (Value m BoolType))

-- conditional instruction support (cmovcc, jcc)
conditionalDefs :: [(String, ConditionalDef)]
conditionalDefs = [ mk "a"  cond_a
                  , mk "ae" cond_ae
                  , mk "b"  cond_b
                  , mk "be" cond_be
                  , mk "g"  cond_g
                  , mk "ge" cond_ge
                  , mk "l"  cond_l
                  , mk "le" cond_le
                  , mk "o"  cond_o
                  , mk "p"  cond_p
                  , mk "s"  cond_s
                  , mk "z"  cond_z
                  , mk "e"  cond_z
                  , mk "ne" cond_nz
                  , mk "no" cond_no
                  , mk "np" cond_np
                  , mk "ns" cond_ns
                  , mk "nz" cond_nz
                  ]
  where mk :: String
          -> (forall m . Semantics m => m (Value m BoolType))
          -> (String, ConditionalDef)
        mk k v = (k, ConditionalDef v)
