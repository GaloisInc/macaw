{- |

This module defines a relational abstract domain for tracking bounds
checks emitted by the compiler on registers and stack location.  This is
built on top of an underlying stack pointer tracking domain so that we
can include checks on stack locations and maintain constraints between
known equivalent values.

-}
module Data.Macaw.AbsDomain.JumpBounds
  ( -- * Range predicates
    RangePred(..)
  , rangeNotTotal
  , SubRange(..)
  , BlockStartRangePred
    -- * Initial jump bounds
  , InitJumpBounds
  , initBndsMap
  , initRngPredMap
  , functionStartBounds
  , ppInitJumpBounds
  , joinInitialBounds
    -- * IntraJumpBounds
  , IntraJumpBounds
  , blockEndBounds
  , postCallBounds
  , postJumpBounds
  , BranchBounds(..)
  , postBranchBounds
  , unsignedUpperBound
    -- * Jump Targets
  , IntraJumpTarget
  ) where

import Data.Macaw.AbsDomain.JumpBounds.Internal
