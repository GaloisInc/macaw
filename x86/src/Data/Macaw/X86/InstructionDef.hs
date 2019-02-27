{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the instruction def type, which contains the
semantic definition of a function.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.X86.InstructionDef
  ( InstructionDef
  , InstructionSemantics(..)
  , defInstruction
  , defVariadic
  , defConditionals
    -- * Nullary function helper
  , defNullary
  , defNullaryPrefix
    -- * Unary instruction helpers
  , defUnary
    -- * Binary instruction helpers
  , defBinary
  , defBinaryLV
  , defBinaryLVpoly
  , defBinaryLVge
  , defBinaryKnown
  , defBinaryXMMV
  , defBinaryLL
    -- * Ternary instruction helpers
  , defTernary
  , defTernaryLVV
  ) where

import qualified Flexdis86 as F
import           Data.Macaw.Types
import           Data.Parameterized.NatRepr
import           GHC.TypeLits (KnownNat)

import           Data.Macaw.X86.Conditions
import           Data.Macaw.X86.Generator
import           Data.Macaw.X86.Getters
import           Data.Macaw.X86.Monad

type Addr s = Expr s (BVType 64)
type BVExpr s w = Expr s (BVType w)

-- This is a wrapper around the semantics of an instruction.
newtype InstructionSemantics
      = InstructionSemantics { _unInstructionSemantics
                               :: forall st ids
                               .  F.InstructionInstance
                               -> X86Generator st ids ()
                             }

-- | The information needed to define an instruction semantics.
type InstructionDef = (String, InstructionSemantics)

-- | Create a instruction that potentially takes any number of arguments.
defInstruction :: String
            -> (forall st ids . F.InstructionInstance -> X86Generator st ids ())
            -> InstructionDef
defInstruction mnemonic f = (mnemonic, InstructionSemantics f)

-- | Create a instruction that potentially takes any number of arguments.
defVariadic :: String
            -> (forall st ids .F.LockPrefix -> [F.Value] -> X86Generator st ids ())
            -> InstructionDef
defVariadic mnem f = defInstruction mnem (\ii -> f (F.iiLockPrefix ii) (fst <$> F.iiArgs ii))

-- | Define an instruction that expects no arguments.
defNullary :: String
           -> (forall st ids . X86Generator st ids ())
           -> InstructionDef
defNullary mnem f = defVariadic mnem (\_ _ -> f)

-- | Define an instruction that expects no arguments other than a prefix
defNullaryPrefix :: String
                 -> (forall st ids . F.LockPrefix -> X86Generator st ids ())
                 -> InstructionDef
defNullaryPrefix mnem f = defVariadic mnem (\pfx _ -> f pfx)

-- | Define an instruction that expects a single argument
defUnary :: String
            -- ^ Instruction mnemonic
         -> (forall st ids . F.LockPrefix -> F.Value -> X86Generator st ids ())
             -- ^ Sementic definition
         -> InstructionDef
defUnary mnem f = defVariadic mnem $ \pfx vs ->
  case vs of
    [v]   -> f pfx v
    _     -> fail $ "defUnary: " ++ mnem ++ " expecting 1 arguments, got " ++ show (length vs)

-- | Define an instruction that expects two arguments.
defBinary :: String
          -> (forall st ids
               .  F.InstructionInstance
               -> F.Value
               -> F.Value
               -> X86Generator st ids ())
          -> InstructionDef
defBinary mnem f = defInstruction mnem $ \ii ->
  case F.iiArgs ii of
    [(v,_), (v',_)]   -> f ii v v'
    _         -> fail $ "defBinary: " ++ mnem ++ ": expecting 2 arguments, got " ++ show (length (F.iiArgs ii))

defBinaryLV :: String
      -> (forall st ids n
          . SupportedBVWidth n
          => Location (Addr ids) (BVType n)
          -> Expr ids (BVType n)
          -> X86Generator st ids ())
      -> InstructionDef
defBinaryLV mnem f = defBinary mnem $ \_ loc val -> do
  SomeBV l <- getSomeBVLocation loc
  v <- getSignExtendedValue val (typeWidth l)
  f l v

-- | This defines a instruction that expects a location and a value that may have
-- differing widths
defBinaryLVpoly :: String
                 -> (forall st ids n n'
                    . (SupportedBVWidth n, 1 <= n')
                    => Location (Addr ids) (BVType n)
                    -> BVExpr ids n'
                    -> X86Generator st ids ())
                 -> InstructionDef
defBinaryLVpoly mnem f = defBinary mnem $ \_ loc val -> do
  SomeBV l <- getSomeBVLocation loc
  SomeBV v <- getSomeBVValue val
  f l v

-- | This defines a instruction that expects a location and a value that may have
-- differing widths, but the location must be larger than the value.
defBinaryLVge :: String
              -> (forall st ids n n'
                  . (SupportedBVWidth n, 1 <= n', n' <= n)
                  => Location (Addr ids) (BVType n)
                  -> Expr ids (BVType n')
                  -> X86Generator st ids ())
              -> InstructionDef
defBinaryLVge mnem f = defBinaryLVpoly mnem $ \l v -> do
  Just LeqProof <- return $ testLeq (typeWidth v) (typeWidth l)
  f l v

-- | Define an instruction from a function with fixed widths known at compile time.
defBinaryKnown :: (KnownNat n, KnownNat n')
               => String
               -> (forall st ids . Location (Addr ids) (BVType n) -> BVExpr ids n' -> X86Generator st ids ())
               -> InstructionDef
defBinaryKnown mnem f = defBinary mnem $ \_ loc val -> do
  l  <- getBVLocation loc knownNat
  v  <- getBVValue val knownNat
  f l v

defBinaryXMMV :: ( KnownNat n
                 , 1 <= n
                 )
              => String
              -> (forall st ids
                  . Location (Addr ids) XMMType
                  -> Expr ids (BVType n)
                  -> X86Generator st ids ())
              -> InstructionDef
defBinaryXMMV mnem f = defBinary mnem $ \_ loc val -> do
  l <- getBVLocation loc n128
  v <- truncateBVValue knownNat =<< getSomeBVValue val
  f l v

defBinaryLL :: String
          -> (forall st ids n
              . SupportedBVWidth n
              => F.LockPrefix
              -> Location (Expr ids (BVType 64)) (BVType n)
              -> Location (Expr ids (BVType 64)) (BVType n)
              -> X86Generator st ids ())
          -> InstructionDef
defBinaryLL mnem f = defBinary mnem $ \ii loc loc' -> do
  SomeBV l <- getSomeBVLocation loc
  l'       <- getBVLocation loc' (typeWidth l)
  f (F.iiLockPrefix ii) l l'

-- | Define an instruction that expects three arguments.
defTernary :: String
           -> (forall st ids . F.LockPrefix -> F.Value -> F.Value -> F.Value -> X86Generator st ids ())
           -> InstructionDef
defTernary mnem f = defVariadic mnem $ \pfx vs -> do
  case vs of
    [v, v', v''] -> f pfx v v' v''
    _ ->
      fail $ "defTernary: " ++ mnem ++ ": expecting 3 arguments, got " ++ show (length vs)

defTernaryLVV :: String
              -> (forall st ids k n
                  . (SupportedBVWidth n, 1 <= k, k <= n)
                  => Location (Addr ids) (BVType n)
                  -> BVExpr ids n
                  -> BVExpr ids k
                  -> X86Generator st ids ())
              -> InstructionDef
defTernaryLVV mnem f = defTernary mnem $ \_ loc val1 val2 -> do
  SomeBV l <- getSomeBVLocation loc
  v1 <- getBVValue val1 (typeWidth l)
  SomeBV v2 <- getSomeBVValue val2
  Just LeqProof <- return $ testLeq (typeWidth v2) (typeWidth v1)
  f l v1 v2

-- | This generates a list of instruction definitinos -- one for each conditional predicate.
defConditionals :: String
                -> (String
                    -> (forall st ids .  X86Generator st ids (Expr ids BoolType))
                    -> InstructionDef)
                -> [InstructionDef]
defConditionals pfx mkop = mk <$> conditionalDefs
  where
    mk :: (String, ConditionalDef) -> InstructionDef
    mk (suffix, ConditionalDef sop) = mkop (pfx ++ suffix) sop
