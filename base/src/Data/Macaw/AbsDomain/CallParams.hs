{-# LANGUAGE DataKinds #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}

module Data.Macaw.AbsDomain.CallParams
  ( CallParams(..)
  ) where

import qualified Data.Kind as Kind
import           Data.Macaw.Types

-- | Minimal information needed to parse a function call/system call
data CallParams (r :: Type -> Kind.Type)
   = CallParams { postCallStackDelta :: Integer
                  -- ^ Amount stack should shift after call.
                , stackGrowsDown :: !Bool
                  -- ^ Returns true if stack grows down
                , preserveReg        :: forall tp . r tp -> Bool
                  -- ^ Return true if a register value is preserved by
                  -- a call.
                  --
                  -- We assume stack pointer and instruction pointer
                  -- are preserved, so the return value for these does not matter.
                }
