{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeFamilies #-}

{-# LANGUAGE GADTs #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.ARM.Eval
    ( mkInitialAbsState
    )
    where

import           Control.Lens ( (&) )
import           Data.Macaw.ARM.Arch
import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM

-- | Set up an initial abstract state that holds at the beginning of a basic
-- block.
--
-- The 'MM.Memory' is the mapped memory region
--
-- The 'ArchSegmentOff' is the start address of the basic block.
--
mkInitialAbsState :: (ARMArchConstraints arm, ArchStmt arm ~ ARMStmt)
                  => proxy arm
                  -> MM.Memory (RegAddrWidth (ArchReg arm))
                  -> ArchSegmentOff arm
                  -> MA.AbsBlockState (ArchReg arm)
mkInitialAbsState _ _mem startAddr =
    MA.top & MA.setAbsIP startAddr
