{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE ImportQualifiedPost #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | Manipulating C-style null-terminated strings
module Data.Macaw.Symbolic.Memory.Strings (
  loadConcreteString,
  loadConcretelyNullTerminatedString,
  loadSymbolicString,
  -- * Low-level string loading primitives
  macawLoader,
) where

import Control.Lens ((^.))
import Control.Monad.IO.Class (MonadIO, liftIO)
import Control.Monad.State.Strict qualified as State
import Data.Macaw.CFG qualified as MC
import Data.Macaw.Memory (Endianness(LittleEndian))
import Data.Macaw.Symbolic (MacawExt)
import Data.Macaw.Symbolic qualified as DMS
import Data.Macaw.Symbolic.MemOps (getMem)
import Data.Parameterized.NatRepr qualified as NatRepr
import Data.Word (Word8)
import Lang.Crucible.Backend qualified as LCB
import Lang.Crucible.Backend.Online qualified as LCBO
import Lang.Crucible.LLVM.MemModel qualified as LCLM
import Lang.Crucible.LLVM.MemModel.Strings qualified as LCLMS
import Lang.Crucible.Simulator qualified as C
import Lang.Crucible.Simulator.ExecutionTree qualified as C
import What4.Expr.Builder qualified as WEB
import What4.Interface qualified as WI
import What4.Protocol.Online qualified as WPO

-- Helper, not exported
loadString ::
  ( LCB.IsSymBackend sym bak
  , LCLM.HasPtrWidth (MC.ArchAddrWidth arch)
  , LCLM.HasLLVMAnn sym
  , MC.MemWidth (MC.ArchAddrWidth arch)
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  C.GlobalVar LCLM.Mem ->
  DMS.MemModelConfig p sym arch LCLM.Mem ->
  C.SimState p sym (MacawExt arch) rtp f args ->
  LCLM.LLVMPtr sym (MC.ArchAddrWidth arch) ->
  -- | Maximum number of characters to read
  Maybe Int ->
  LCLMS.ByteChecker (State.StateT (C.SimState p sym (MacawExt arch) rtp f args) IO) sym bak ([a] -> [a]) [a] ->
  IO ([a], C.SimState p sym (MacawExt arch) rtp f args)
loadString bak memVar mmConf st0 ptr limit checker = do
  let loader = macawLoader memVar mmConf
  mem <- getMem st0 memVar
  flip State.runStateT st0 $
    case limit of
      Nothing -> LCLMS.loadBytes bak mem id ptr loader checker
      Just l ->
        let byteChecker = LCLMS.withMaxChars l (\f -> pure (f [])) checker in
        LCLMS.loadBytes bak mem (id, 0) ptr loader byteChecker

-- | Load a concrete null-terminated string from memory.
--
-- The string must be fully concrete. If a maximum number of characters is
-- provided, no more than that number of characters will be read. In either
-- case, 'loadConcreteString' will stop reading if it encounters a null
-- terminator.
--
-- c.f. 'LCLMS.loadString', which does the same thing for LLVM.
loadConcreteString ::
  ( LCLM.HasPtrWidth (MC.ArchAddrWidth arch)
  , LCLM.HasLLVMAnn sym
  , MC.MemWidth (MC.ArchAddrWidth arch)
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  DMS.MemModelConfig p sym arch LCLM.Mem ->
  C.SimState p sym (MacawExt arch) rtp f args ->
  LCLM.LLVMPtr sym (MC.ArchAddrWidth arch) ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO ([Word8], C.SimState p sym (MacawExt arch) rtp f args)
loadConcreteString memVar mmConf st0 ptr limit =
  C.withBackend (st0 ^. C.stateContext) $ \bak ->
    loadString bak memVar mmConf st0 ptr limit LCLMS.fullyConcreteNullTerminatedString

-- | Load a null-terminated string (with a concrete null terminator) from memory.
--
-- The string must contain a concrete null terminator. If a maximum number of
-- characters is provided, no more than that number of characters will be read.
-- In either case, 'loadConcretelyNullTerminatedString' will stop reading if it
-- encounters a (concretely) null terminator.
--
-- Note that the loaded string may actually be smaller than the returned list if
-- any of the symbolic bytes are equal to 0.
--
-- c.f. 'LCLMS.loadConcretelyNullTerminatedString', which does the same thing
-- for LLVM.
loadConcretelyNullTerminatedString ::
  ( LCLM.HasPtrWidth (MC.ArchAddrWidth arch)
  , LCLM.HasLLVMAnn sym
  , MC.MemWidth (MC.ArchAddrWidth arch)
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  DMS.MemModelConfig p sym arch LCLM.Mem ->
  C.SimState p sym (MacawExt arch) rtp f args ->
  LCLM.LLVMPtr sym (MC.ArchAddrWidth arch) ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO ([WI.SymBV sym 8], C.SimState p sym (MacawExt arch) rtp f args)
loadConcretelyNullTerminatedString memVar mmConf st0 ptr limit =
  C.withBackend (st0 ^. C.stateContext) $ \bak ->
    loadString bak memVar mmConf st0 ptr limit LCLMS.concretelyNullTerminatedString

-- | Load a null-terminated string from memory.
--
-- Consults an SMT solver to check if any of the loaded bytes are known to be
-- null (0). If a maximum number of characters is provided, no more than that
-- number of charcters will be read. In either case, 'loadSymbolicString' will
-- stop reading if it encounters a null terminator.
--
-- Note that the loaded string may actually be smaller than the returned list if
-- any of the symbolic bytes are equal to 0.
--
-- c.f. 'LCLMS.loadSymbolicString', which does the same thing for LLVM.
loadSymbolicString ::
  ( LCLM.HasPtrWidth (MC.ArchAddrWidth arch)
  , LCLM.HasLLVMAnn sym
  , MC.MemWidth (MC.ArchAddrWidth arch)
  , LCB.IsSymBackend sym bak
  , sym ~ WEB.ExprBuilder scope st fs
  , bak ~ LCBO.OnlineBackend solver scope st fs
  , WPO.OnlineSolver solver
  , ?memOpts :: LCLM.MemOptions
  ) =>
  bak ->
  C.GlobalVar LCLM.Mem ->
  DMS.MemModelConfig p sym arch LCLM.Mem ->
  C.SimState p sym (MacawExt arch) rtp f args ->
  LCLM.LLVMPtr sym (MC.ArchAddrWidth arch) ->
  -- | Maximum number of characters to read
  Maybe Int ->
  IO ([WI.SymBV sym 8], C.SimState p sym (MacawExt arch) rtp f args)
loadSymbolicString bak memVar mmConf st0 ptr limit =
  loadString bak memVar mmConf st0 ptr limit LCLMS.nullTerminatedString

---------------------------------------------------------------------
-- * Low-level string loading primitives

-- | A 'LCLMS.ByteLoader' that uses 'DMS.doReadMemModel'
macawLoader ::
  ( State.MonadState (C.SimState p sym (MacawExt arch) rtp f args) m
  , MonadIO m
  , LCLM.HasPtrWidth (MC.ArchAddrWidth arch)
  , MC.MemWidth (MC.ArchAddrWidth arch)
  , LCLM.HasLLVMAnn sym
  , ?memOpts :: LCLM.MemOptions
  ) =>
  C.GlobalVar LCLM.Mem ->
  DMS.MemModelConfig p sym arch LCLM.Mem ->
  LCLMS.ByteLoader m sym bak (MC.ArchAddrWidth arch)
macawLoader memVar mmConf =
  LCLMS.ByteLoader $ \_bak ptr -> do
    -- note that endianness is arbitrary because we're reading one byte
    let readInfo = MC.BVMemRepr (NatRepr.knownNat @1) LittleEndian
    let addrWidth = MC.addrWidthRepr ?ptrWidth
    let ptrTy = LCLM.LLVMPointerRepr (MC.addrWidthNatRepr addrWidth)
    let regEntry = C.RegEntry ptrTy ptr
    st <- State.get
    (v, st') <- liftIO (DMS.doReadMemModel memVar mmConf addrWidth readInfo regEntry st)
    State.put st'
    pure v
