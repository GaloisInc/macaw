{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.PPC.Eval (
  mkInitialAbsState,
  absEvalArchFn,
  absEvalArchStmt,
  postCallAbsState,
  preserveRegAcrossSyscall
  ) where

import           GHC.TypeLits

import           Control.Lens ( (&) )
import qualified Data.Set as S

import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import qualified Data.Macaw.Memory as MM
import           Data.Parameterized.Some ( Some(..) )

import           Data.Macaw.PPC.PPCReg

preserveRegAcrossSyscall :: (ArchReg ppc ~ PPCReg ppc, 1 <= RegAddrWidth (PPCReg ppc))
                         => proxy ppc
                         -> ArchReg ppc tp
                         -> Bool
preserveRegAcrossSyscall proxy r = S.member (Some r) (linuxSystemCallPreservedRegisters proxy)

-- | Set up an initial abstract state that holds at the beginning of a basic
-- block.
--
-- The 'MM.Memory' is the mapped memory region
--
-- The 'ArchSegmentOff' is the start address of the basic block.
--
-- Note that we don't initialize the abstract stack.  On PowerPC, there are no
-- initial stack entries (since the return address is in the link register).
mkInitialAbsState :: (PPCWidth ppc)
                  => proxy ppc
                  -> MM.Memory (RegAddrWidth (ArchReg ppc))
                  -> ArchSegmentOff ppc
                  -> MA.AbsBlockState (ArchReg ppc)
mkInitialAbsState _ _mem startAddr =
  MA.top & MA.setAbsIP startAddr

absEvalArchFn :: proxy ppc
              -> AbsProcessorState (ArchReg ppc) ids
              -> ArchFn ppc (Value ppc ids) tp
              -> AbsValue (RegAddrWidth (ArchReg ppc)) tp
absEvalArchFn = undefined

-- | For now, none of the architecture-specific statements have an effect on the
-- abstract value.
absEvalArchStmt :: proxy ppc
                -> AbsProcessorState (ArchReg ppc) ids
                -> ArchStmt ppc ids
                -> AbsProcessorState (ArchReg ppc) ids
absEvalArchStmt _ s _ = s

postCallAbsState :: proxy ppc
                 -> AbsBlockState (ArchReg ppc)
                 -> ArchSegmentOff ppc
                 -> AbsBlockState (ArchReg ppc)
postCallAbsState = undefined
