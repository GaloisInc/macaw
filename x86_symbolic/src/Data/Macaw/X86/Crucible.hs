{-# Language GADTs #-}
{-# Language RankNTypes #-}
{-# Language KindSignatures #-}
{-# Language LambdaCase #-}
{-# Language DataKinds #-}
{-# Language TypeApplications #-}
{-# Language TypeFamilies #-}
{-# Language TypeOperators #-}
{-# Language ScopedTypeVariables #-}
{-# Language EmptyCase #-}
{-# Language MultiWayIf #-}
{-# Language PatternGuards #-}
{-# Language PatternSynonyms #-}
{-# Language RecordWildCards #-}
{-# Language FlexibleContexts #-}
{-# Language ImplicitParams #-}
module Data.Macaw.X86.Crucible
  ( -- * Uninterpreted functions
    SymFuns(..), newSymFuns

    -- * Instruction interpretation
  , MissingSemantics(..)
  , funcSemantics
  , stmtSemantics
  , termSemantics

    -- * Atom wrapper
  , AtomWrapper(..)
  , liftAtomMap
  , liftAtomTrav
  , liftAtomIn
  ) where

import           Control.Exception (Exception, throw)
import           Control.Lens ((^.))
import           Control.Monad
import           Data.Bits hiding (xor)
import qualified Data.BitVector.Sized as BV
import qualified Data.Functor.Identity as I
import           Data.Kind ( Type )
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Context.Unsafe (empty,extend)
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Utils.Endian (Endian(..))
import qualified Data.Parameterized.Vector as PV
import qualified Data.Vector as DV
import           Data.Word (Word8)
import           GHC.TypeLits (KnownNat)
import           Prettyprinter

import           What4.Concrete
import           What4.Interface hiding (IsExpr)
import           What4.InterpretedFloatingPoint

import           Lang.Crucible.Backend (IsSymInterface, assert, IsSymBackend, HasSymInterface(..))
import           Lang.Crucible.CFG.Expr
import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Simulator.Evaluation as C
import           Lang.Crucible.Simulator.ExecutionTree
import           Lang.Crucible.Simulator.Intrinsics (IntrinsicTypes)
import           Lang.Crucible.Simulator.RegMap
import           Lang.Crucible.Syntax
import           Lang.Crucible.Types
import qualified Lang.Crucible.Vector as V

import           Lang.Crucible.LLVM.MemModel
                   ( LLVMPointerType
                   , Mem
                   , MemOptions
                   , HasLLVMAnn
                   , ptrAdd
                   , projectLLVM_bv
                   , pattern LLVMPointerRepr
                   , llvmPointer_bv
                   )
import qualified Lang.Crucible.LLVM.MemModel.Pointer as Pointer

import qualified Data.Macaw.CFG.Core as M
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as M
import           Data.Macaw.Symbolic
import           Data.Macaw.Symbolic.Backend hiding (bvLit)
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.X86 as M
import qualified Data.Macaw.X86.ArchTypes as M

import           Prelude


type S p sym rtp bs r ctx =
  CrucibleState p sym (MacawExt M.X86_64) rtp bs r ctx

funcSemantics
  :: (IsSymInterface sym, ToCrucibleType mt ~ t)
  => SymFuns sym
  -> M.X86PrimFn (AtomWrapper (RegEntry sym)) mt
  -> S p sym rtp bs r ctx
  -> IO (RegValue sym t, S p sym rtp bs r ctx)
funcSemantics fs x s =
  withBackend (s^.stateContext) $ \bak ->
    do let sym = Sym
                 { symBackend = bak
                 , symIface = backendGetSym bak
                 , symTys   = s^.stateIntrinsicTypes
                 , symFuns  = fs
                 }
       v <- pureSem sym x
       return (v,s)

withConcreteCountAndDir
  :: (IsSymInterface sym, 1 <= w)
  => S p sym rtp bs r ctx
  -> M.RepValSize w
  -> (AtomWrapper (RegEntry sym) (M.BVType 64))
  -> (AtomWrapper (RegEntry sym) M.BoolType)
  -> (S p sym rtp bs r ctx -> (SymBV sym 64) -> IO (S p sym rtp bs r ctx))
  -> IO (RegValue sym UnitType, S p sym rtp bs r ctx)
withConcreteCountAndDir state val_size wrapped_count _wrapped_dir func =
  withBackend (state^.stateContext) $ \bak -> do
  let sym = backendGetSym bak
  let val_byte_size :: Integer
      val_byte_size = fromIntegral $ M.repValSizeByteCount val_size
  bv_count <- toValBV bak wrapped_count
  case asConcrete bv_count of
    Just (ConcreteBV _ count) -> do
      res_crux_state <- foldM func state
        =<< mapM (\index -> bvLit sym knownNat $ BV.mkBV knownNat $ index * val_byte_size)
          -- [0..((if dir then 1 else -1) * (count - 1))]
          [0..(BV.asUnsigned count - 1)]
      return ((), res_crux_state)
    Nothing -> error $ "Unsupported symbolic count in rep stmt: "

-- | An 'Exception' thrown when Crucible attempts to execute an instruction for
-- which we have no semantics. The 'String' fields are human-readable messages.
data MissingSemantics where
  MissingPrimFnSemantics :: forall sym mt. M.X86PrimFn (AtomWrapper (RegEntry sym)) mt -> MissingSemantics
  MissingStmtSemantics :: forall sym. M.X86Stmt (AtomWrapper (RegEntry sym)) -> MissingSemantics
  MissingTermSemantics :: forall sym. M.X86TermStmt (AtomWrapper (RegEntry sym)) -> MissingSemantics

instance Show MissingSemantics where
  show = show . pretty

instance Exception MissingSemantics

instance Pretty MissingSemantics where
  pretty =
    \case
      MissingPrimFnSemantics fn ->
        pretty "Symbolic execution semantics for x86 primitive function are not implemented yet:"
          <+> I.runIdentity (MC.ppArchFn (I.Identity . liftAtomIn (pretty . regType)) fn)
      MissingStmtSemantics stmt ->
        pretty "Symbolic execution semantics for x86 statement are not implemented yet:"
          <+> MC.ppArchStmt (liftAtomIn (pretty . regType)) stmt
      MissingTermSemantics term ->
        pretty "Symbolic execution semantics for x86 terminators are not implemented yet:"
          -- We can't print out sub-terms that are RegEntry; however, since
          -- none of the x86 terminators contain nested dynamic values, we
          -- don't need to.
          <+> MC.ppArchTermStmt (error "Can't print RegEntry") term

stmtSemantics
  :: (IsSymInterface sym, HasLLVMAnn sym, ?memOpts :: MemOptions)
  => SymFuns sym
  -> C.GlobalVar Mem
  -> GlobalMap sym Mem (M.ArchAddrWidth M.X86_64)
  -> M.X86Stmt (AtomWrapper (RegEntry sym))
  -> S p sym rtp bs r ctx
  -> IO (RegValue sym UnitType, S p sym rtp bs r ctx)
stmtSemantics _sym_funs global_var_mem globals stmt state =
  withBackend (state^.stateContext) $ \bak ->
  let sym = backendGetSym bak in
  case stmt of
    M.RepMovs val_size (AtomWrapper dest) (AtomWrapper src) count dir ->
      withConcreteCountAndDir state val_size count dir $ \acc_state offset -> do
        let mem_repr = M.repValSizeMemRepr val_size
        curr_dest_ptr <- ptrAdd sym knownNat (regValue dest) offset
        curr_src_ptr <- ptrAdd sym knownNat (regValue src) offset
        -- Get simulator and memory
        mem <- getMem acc_state global_var_mem
        -- Resolve source pointer
        resolvedSrcPtr <- tryGlobPtr bak mem globals curr_src_ptr
        -- Read resolvePtr
        val <- doReadMem bak mem M.Addr64 mem_repr resolvedSrcPtr
        -- Resolve destination pointer
        resolvedDestPtr <- tryGlobPtr bak mem globals curr_dest_ptr
        afterWriteMem <- doWriteMem bak mem M.Addr64 mem_repr resolvedDestPtr val
        -- Update the final state
        pure $! setMem acc_state global_var_mem afterWriteMem
    M.RepStos val_size (AtomWrapper dest) (AtomWrapper val) count dir ->
      withConcreteCountAndDir state val_size count dir $ \acc_state offset -> do
        let mem_repr = M.repValSizeMemRepr val_size
        -- Get simulator and memory
        mem <- getMem acc_state global_var_mem
        -- Resolve address to write to.
        curr_dest_ptr <- ptrAdd sym knownNat (regValue dest) offset
        resolvedDestPtr <- tryGlobPtr bak mem globals curr_dest_ptr
        -- Perform write
        afterWriteMem <- doWriteMem bak mem M.Addr64 mem_repr resolvedDestPtr (regValue val)
        -- Update the final state
        pure $! setMem acc_state global_var_mem afterWriteMem
    _ -> throw (MissingStmtSemantics stmt)

-- | Dynamic semantics for x86-specific arch terminators
termSemantics :: (IsSymInterface sym)
              => SymFuns sym
              -> M.X86TermStmt (AtomWrapper (RegEntry sym))
              -> S p sym rtp bs r ctx
              -> IO (RegValue sym UnitType, S p sym rtp bs r ctx)
termSemantics _fs term _s = throw (MissingTermSemantics term)

data Sym s bak =
  Sym { symBackend :: bak
      , symIface :: s
      , symTys   :: IntrinsicTypes s
      , symFuns  :: SymFuns s
      }

data SymFuns s = SymFuns
  { fnAesEnc ::
      SymFn s (EmptyCtx ::> BaseBVType 128 ::> BaseBVType 128) (BaseBVType 128)
    -- ^ One round of AES encryption

  , fnAesEncLast ::
      SymFn s (EmptyCtx ::> BaseBVType 128 ::> BaseBVType 128) (BaseBVType 128)
    -- ^ Last round of AES encryption

  , fnAesDec ::
      SymFn s (EmptyCtx ::> BaseBVType 128 ::> BaseBVType 128) (BaseBVType 128)
    -- ^ One round of AES decryption

  , fnAesDecLast ::
      SymFn s (EmptyCtx ::> BaseBVType 128 ::> BaseBVType 128) (BaseBVType 128)
    -- ^ Last round of AES decryption

  , fnAesKeyGenAssist ::
      SymFn s (EmptyCtx ::> BaseBVType 128 ::> BaseBVType 8) (BaseBVType 128)
    -- ^ Assist in expanding AES cipher key

  , fnAesIMC ::
      SymFn s (EmptyCtx ::> BaseBVType 128) (BaseBVType 128)
    -- ^ Perform the AES InvMixColumn transformation

  , fnClMul ::
      SymFn s (EmptyCtx ::> BaseBVType 64 ::> BaseBVType 64) (BaseBVType 128)
    -- ^ Carryless multiplication

  , fnShasigma0 ::
      SymFn s (EmptyCtx ::> BaseBVType 32) (BaseBVType 32)
    -- ^ SHA256 sigma0

  , fnShasigma1 ::
      SymFn s (EmptyCtx ::> BaseBVType 32) (BaseBVType 32)
    -- ^ SHA256 sigma1

  , fnShaSigma0 ::
      SymFn s (EmptyCtx ::> BaseBVType 32) (BaseBVType 32)
    -- ^ SHA256 Sigma0

  , fnShaSigma1 ::
      SymFn s (EmptyCtx ::> BaseBVType 32) (BaseBVType 32)
    -- ^ SHA256 Sigma1

  , fnShaCh ::
      SymFn s (EmptyCtx ::> BaseBVType 32 ::> BaseBVType 32 ::> BaseBVType 32) (BaseBVType 32)
    -- ^ SHA256 Ch

  , fnShaMaj ::
      SymFn s (EmptyCtx ::> BaseBVType 32 ::> BaseBVType 32 ::> BaseBVType 32) (BaseBVType 32)
    -- ^ SHA256 Maj
  }


-- | Generate uninterpreted functions for some of the more complex instructions.
newSymFuns :: forall sym. IsSymInterface sym => sym -> IO (SymFuns sym)
newSymFuns s =
  do fnAesEnc <- bin "aesEnc"
     fnAesEncLast <- bin "aesEncLast"
     fnAesDec <- bin "aesDecLast"
     fnAesDecLast <- bin "aesDecLast"
     fnAesKeyGenAssist <- bin "aesKeyGenAssist"
     fnClMul <- bin "clMul"
     fnAesIMC <- un "aesIMC"
     fnShasigma0 <- un "sigma0"
     fnShasigma1 <- un "sigma1"
     fnShaSigma0 <- un "Sigma0"
     fnShaSigma1 <- un "Sigma1"
     fnShaCh <- tern "Ch"
     fnShaMaj <- tern "Maj"
     return SymFuns { .. }

  where
  un :: ( KnownRepr BaseTypeRepr a
        , KnownRepr BaseTypeRepr b
        ) =>
        String -> IO (SymFn sym (EmptyCtx ::> a) b)
  un name = freshTotalUninterpFn s (safeSymbol name) (extend empty knownRepr) knownRepr
  bin :: ( KnownRepr BaseTypeRepr a
         , KnownRepr BaseTypeRepr b
         , KnownRepr BaseTypeRepr c
         ) =>
         String -> IO (SymFn sym (EmptyCtx ::> a ::> b) c)
  bin name = freshTotalUninterpFn s (safeSymbol name) (extend (extend empty knownRepr) knownRepr) knownRepr
  tern :: ( KnownRepr BaseTypeRepr a
          , KnownRepr BaseTypeRepr b
          , KnownRepr BaseTypeRepr c
          , KnownRepr BaseTypeRepr d
          ) =>
         String -> IO (SymFn sym (EmptyCtx ::> a ::> b ::> c) d)
  tern name = freshTotalUninterpFn s (safeSymbol name) (extend (extend (extend empty knownRepr) knownRepr) knownRepr) knownRepr

-- | Use @Sym sym@ to to evaluate an app.
evalApp' :: forall sym bak f t .
  (IsSymBackend sym bak) =>
  Sym sym bak ->
  (forall utp . f utp -> IO (RegValue sym utp)) ->
  App () f t ->
  IO (RegValue sym t)
evalApp' sym ev = C.evalApp (symBackend sym) (symTys sym) logger evalExt ev
  where
  logger _ _ = return ()

  evalExt :: (forall a. g a -> IO (RegValue sym a))
          -> (forall a. EmptyExprExtension g a -> IO (RegValue sym a))
  evalExt _ y  = case y of {}

pureSemSymUn
  :: forall sym bak n. (IsSymBackend sym bak)
  => Sym sym bak
  -> (SymFuns sym -> SymFn sym (EmptyCtx ::> BaseBVType n) (BaseBVType n))
  -> AtomWrapper (RegEntry sym) (M.BVType n)
  -> IO (RegValue sym (ToCrucibleType (M.BVType n)))
pureSemSymUn sym proj x =
  do let f = proj (symFuns sym)
         s = symIface sym
     src1 <- toValBV (symBackend sym) x
     let ps = extend empty src1
     llvmPointer_bv s =<< applySymFn s f ps

pureSemSymBin
  :: forall sym bak n. (IsSymBackend sym bak)
  => Sym sym bak
  -> (SymFuns sym -> SymFn sym (EmptyCtx ::> BaseBVType n ::> BaseBVType n) (BaseBVType n))
  -> AtomWrapper (RegEntry sym) (M.BVType n)
  -> AtomWrapper (RegEntry sym) (M.BVType n)
  -> IO (RegValue sym (ToCrucibleType (M.BVType n)))
pureSemSymBin sym proj x y =
  do let f = proj (symFuns sym)
         s = symIface sym
     src1 <- toValBV (symBackend sym) x
     src2 <- toValBV (symBackend sym) y
     let ps = extend (extend empty src1) src2
     llvmPointer_bv s =<< applySymFn s f ps

pureSemSymTern
  :: forall sym bak n. (IsSymBackend sym bak)
  => Sym sym bak
  -> (SymFuns sym -> SymFn sym (EmptyCtx ::> BaseBVType n ::> BaseBVType n ::> BaseBVType n) (BaseBVType n))
  -> AtomWrapper (RegEntry sym) (M.BVType n)
  -> AtomWrapper (RegEntry sym) (M.BVType n)
  -> AtomWrapper (RegEntry sym) (M.BVType n)
  -> IO (RegValue sym (ToCrucibleType (M.BVType n)))
pureSemSymTern sym proj x y z =
  do let f = proj (symFuns sym)
         s = symIface sym
     src1 <- toValBV (symBackend sym) x
     src2 <- toValBV (symBackend sym) y
     src3 <- toValBV (symBackend sym) z
     let ps = extend (extend (extend empty src1) src2) src3
     llvmPointer_bv s =<< applySymFn s f ps

-- | Semantics for operations that do not affect Crucible's state directly.
pureSem :: forall sym bak mt
        .  (IsSymBackend sym bak)
        => Sym sym bak  {- ^ Handle to the simulator -}
        -> M.X86PrimFn (AtomWrapper (RegEntry sym)) mt {- ^ Instruction -}
        -> IO (RegValue sym (ToCrucibleType mt)) -- ^ Resulting value
pureSem sym fn = do
  let symi = symIface sym
  let bak = symBackend sym
  case fn of
    M.EvenParity x0 ->
      -- See Note [EvenParity Semantics] for why this uses getPointerOffset
      -- (rather than getBitVal)
      do x <- getPointerOffset x0
         evalE sym $ app $ Not $ foldr1 xor [ bvTestBit x i | i <- [ 0 .. 7 ] ]
      where xor a b = app (BoolXor a b)
    M.ReadFSBase    -> throw (MissingPrimFnSemantics fn)
    M.ReadGSBase    -> throw (MissingPrimFnSemantics fn)
    M.GetSegmentSelector _ -> throw (MissingPrimFnSemantics fn)
    M.CPUID{}       -> throw (MissingPrimFnSemantics fn)
    M.CMPXCHG8B{} -> throw (MissingPrimFnSemantics fn)
    M.RDTSC{}       -> throw (MissingPrimFnSemantics fn)
    M.XGetBV {} -> throw (MissingPrimFnSemantics fn)
    M.PShufb sw (AtomWrapper vxs) (AtomWrapper vys) ->
      case sw of
        M.SIMDByteCount_XMM
          | Just pxs <- V.fromList n16 $ DV.toList $ regValue vxs
          , Just pys <- V.fromList n16 $ DV.toList $ regValue vys -> do
              xs <- mapM (pure . ValBV n8 <=< projectLLVM_bv bak) pxs
              ys <- mapM (pure . ValBV n8 <=< projectLLVM_bv bak) pys
              let res = DV.fromList $ V.toList $ shuffleB xs ys
              mapM (llvmPointer_bv (symIface sym) <=< evalE sym) res
        _ -> error "PShufb is not implemented for 64-bit operands"
    M.MemCmp{}      -> throw (MissingPrimFnSemantics fn)
    M.RepnzScas{}   -> throw (MissingPrimFnSemantics fn)
    M.MMXExtend {} -> throw (MissingPrimFnSemantics fn)
    M.X86IDivRem w num1 num2 d -> do
      sDivRem sym w num1 num2 d
    M.X86DivRem  w num1 num2 d -> do
      uDivRem sym w num1 num2 d

    M.SSE_UnaryOp op (_tp :: M.SSE_FloatType ftp) (AtomWrapper x) (AtomWrapper y) -> do
      let f = case op of
                M.SSE_Add  -> iFloatAdd  @_ @(ToCrucibleFloatInfo ftp) symi RNE
                M.SSE_Sub  -> iFloatSub  @_ @(ToCrucibleFloatInfo ftp) symi RNE
                M.SSE_Mul  -> iFloatMul  @_ @(ToCrucibleFloatInfo ftp) symi RNE
                M.SSE_Div  -> iFloatDiv  @_ @(ToCrucibleFloatInfo ftp) symi RNE
                M.SSE_Min  -> iFloatMin  @_ @(ToCrucibleFloatInfo ftp) symi
                M.SSE_Max  -> iFloatMax  @_ @(ToCrucibleFloatInfo ftp) symi
      f (regValue x) (regValue y)

    M.SSE_VectorOp op _n (_tp :: M.SSE_FloatType ftp) (AtomWrapper x) (AtomWrapper y) -> do
      let f = case op of
                M.SSE_Add  -> iFloatAdd  @_ @(ToCrucibleFloatInfo ftp) symi RNE
                M.SSE_Sub  -> iFloatSub  @_ @(ToCrucibleFloatInfo ftp) symi RNE
                M.SSE_Mul  -> iFloatMul  @_ @(ToCrucibleFloatInfo ftp) symi RNE
                M.SSE_Div  -> iFloatDiv  @_ @(ToCrucibleFloatInfo ftp) symi RNE
                M.SSE_Min  -> iFloatMin  @_ @(ToCrucibleFloatInfo ftp) symi
                M.SSE_Max  -> iFloatMax  @_ @(ToCrucibleFloatInfo ftp) symi
      DV.zipWithM f (regValue x) (regValue y)

    M.SSE_Sqrt (_tp :: M.SSE_FloatType ftp) (AtomWrapper x)  -> do
      iFloatSqrt  @_ @(ToCrucibleFloatInfo ftp) symi RTP (regValue x)

    M.SSE_CMPSX op (_tp :: M.SSE_FloatType ftp) (AtomWrapper x) (AtomWrapper y) -> do
      let x' = regValue x
      let y' = regValue y
      case op of
        M.EQ_OQ -> iFloatFpEq @_ @(ToCrucibleFloatInfo ftp) symi x' y'
        M.LT_OS -> iFloatLt @_ @(ToCrucibleFloatInfo ftp) symi x' y'
        M.LE_OS -> iFloatLe @_ @(ToCrucibleFloatInfo ftp) symi x' y'
        M.UNORD_Q -> do
          x_is_nan <- iFloatIsNaN @_ @(ToCrucibleFloatInfo ftp) symi x'
          y_is_nan <- iFloatIsNaN @_ @(ToCrucibleFloatInfo ftp) symi y'
          orPred symi x_is_nan y_is_nan
        M.NEQ_UQ ->
          notPred symi =<< iFloatFpEq @_ @(ToCrucibleFloatInfo ftp) symi x' y'
        M.NLT_US ->
          notPred symi =<< iFloatLt @_ @(ToCrucibleFloatInfo ftp) symi x' y'
        M.NLE_US ->
          notPred symi =<< iFloatLe @_ @(ToCrucibleFloatInfo ftp) symi x' y'
        M.ORD_Q -> do
          x_is_nan <- iFloatIsNaN @_ @(ToCrucibleFloatInfo ftp) symi x'
          y_is_nan <- iFloatIsNaN @_ @(ToCrucibleFloatInfo ftp) symi y'
          notPred symi =<< orPred symi x_is_nan y_is_nan
    M.SSE_UCOMIS (_tp :: M.SSE_FloatType ftp) (AtomWrapper x) (AtomWrapper y) -> do
      let x' = regValue x
      let y' = regValue y
      is_eq    <- iFloatFpEq @_ @(ToCrucibleFloatInfo ftp) symi x' y'
      is_lt    <- iFloatLt @_ @(ToCrucibleFloatInfo ftp)  symi x' y'
      x_is_nan <- iFloatIsNaN @_ @(ToCrucibleFloatInfo ftp) symi x'
      y_is_nan <- iFloatIsNaN @_ @(ToCrucibleFloatInfo ftp) symi y'
      is_unord <- orPred symi x_is_nan y_is_nan
      zf <- orPred symi is_eq is_unord
      cf <- orPred symi is_lt is_unord
      let pf = is_unord
      return $ empty `extend` (RV zf) `extend` (RV pf) `extend` (RV cf)
    M.SSE_CVTSS2SD (AtomWrapper x) ->
      iFloatCast @_ @DoubleFloat @SingleFloat symi knownRepr RNE (regValue x)
    M.SSE_CVTSD2SS (AtomWrapper x) ->
      iFloatCast @_ @SingleFloat @DoubleFloat symi knownRepr RNE (regValue x)
    M.SSE_CVTTSX2SI w (_ :: M.SSE_FloatType ftp) (AtomWrapper x) ->
      llvmPointer_bv symi
        =<< iFloatToSBV @_ @_ @(ToCrucibleFloatInfo ftp) symi w RTZ (regValue x)
    M.SSE_CVTSI2SX tp _ x ->
     iSBVToFloat symi (floatInfoFromSSEType tp) RNE
        =<< toValBV bak x

    M.X87_Extend{} ->  throw (MissingPrimFnSemantics fn)
    M.X87_FAdd{} -> throw (MissingPrimFnSemantics fn)
    M.X87_FSub{} -> throw (MissingPrimFnSemantics fn)
    M.X87_FMul{} -> throw (MissingPrimFnSemantics fn)
    M.X87_FST {} -> throw (MissingPrimFnSemantics fn)

    M.VOp1 w op1 x ->
      case op1 of
        M.VShiftL n -> vecOp1 sym BigEndian w n8 x
                        (V.shiftL (fromIntegral n) (bv 0))

        M.VShiftR n -> vecOp1 sym BigEndian w n8 x
                        (V.shiftR (fromIntegral n) (bv 0))

        M.VShufD mask -> vecOp1 sym LittleEndian w n32 x $ \xs ->
          divExact (V.length xs) n4 $ \i ->
            V.join n4 $ fmap (shuffleD mask)
                      $ V.split i n4 xs

    M.VOp2 w op2 x y ->
      case op2 of
        M.VPOr   -> bitOp2 sym x y (BVOr w)
        M.VPXor  -> bitOp2 sym x y (BVXor w)
        M.VPAnd  -> bitOp2 sym x y (BVAnd w)

        M.VPAlignR s -> vecOp2 sym BigEndian w n8 x y $ \xs ys ->
          divExact (V.length xs) n16 $ \i ->
              V.join n16 $ V.zipWith (vpalign s)
                                     (V.split i n16 xs)
                                     (V.split i n16 ys)

        M.VPShufB -> vecOp2 sym LittleEndian w n8 x y $ \xs ys ->
          divExact (V.length xs) n16 $ \i ->
            V.join n16 $ V.zipWith shuffleB
                                   (V.split i n16 xs)
                                   (V.split i n16 ys)

        M.VPCLMULQDQ i -> unpack2 (symBackend sym) LittleEndian w n64 x y $
          \xs ys ->
          case testEquality (V.length xs) n2 of
            Just Refl ->
              do let v1 = if i `testBit` 0 then V.elemAt n1 xs
                                           else V.elemAt n0 xs
                     v2 = if i `testBit` 4 then V.elemAt n1 ys
                                           else V.elemAt n0 ys

                 x1 <- evalE sym v1
                 x2 <- evalE sym v2
                 let f  = fnClMul (symFuns sym)
                     ps = extend (extend empty x2) x1
                 llvmPointer_bv (symIface sym) =<<
                                  applySymFn (symIface sym) f ps

            _ -> fail "Unepected size for VPCLMULQDQ"

        M.VPUnpackLQDQ -> vecOp2 sym LittleEndian w (knownNat @64) x y $
          \xs ys -> let n = V.length xs
                    in case mul2Plus n of
                         Refl -> V.take n (PV.interleave xs ys)

        M.VPUnpackHQDQ -> vecOp2 sym BigEndian w (knownNat @64) x y $
          \xs ys -> let n = V.length xs
                    in case mul2Plus n of
                         Refl -> V.take n (PV.interleave xs ys)

        M.VAESEnc
          | Just Refl <- testEquality w n128 ->
            do let f = fnAesEnc (symFuns sym)
                   s = symIface sym
               state <- toValBV bak x
               key   <- toValBV bak y
               let ps = extend (extend empty state) key
               llvmPointer_bv s =<< applySymFn s f ps
          | otherwise -> fail "Unexpecte size for AESEnc"

        M.VAESEncLast
          | Just Refl <- testEquality w n128 ->
            do let f = fnAesEncLast (symFuns sym)
                   s = symIface sym
               state <- toValBV bak x
               key   <- toValBV bak y
               let ps     = extend (extend empty state) key
               llvmPointer_bv s =<< applySymFn s f ps
          | otherwise -> fail "Unexpecte size for AESEncLast"

    M.VInsert elNum elSz vec el i ->
      do e <- getBitVal (symBackend sym) el
         vecOp1 sym LittleEndian (natMultiply elNum elSz) elSz vec $ \xs ->
           case mulCancelR elNum (V.length xs) elSz of
             Refl -> V.insertAt i e xs

    M.PointwiseShiftL elNum elSz shSz bits amt ->
      do amt' <- getBitVal (symBackend sym) amt
         vecOp1 sym LittleEndian (natMultiply elNum elSz) elSz bits $ \xs ->
              fmap (\x -> bvShiftL elSz shSz x amt') xs

    M.PointwiseLogicalShiftR elNum elSz shSz bits amt ->
      do amt' <- getBitVal (symBackend sym) amt
         vecOp1 sym LittleEndian (natMultiply elNum elSz) elSz bits $ \xs ->
              fmap (\x -> bvLogicalShiftR elSz shSz x amt') xs

    M.Pointwise2 elNum elSz op v1 v2 ->
      vecOp2 sym LittleEndian (natMultiply elNum elSz) elSz v1 v2 $ \xs ys ->
        V.zipWith (semPointwise op elSz) xs ys

    M.VExtractF128 {} -> throw (MissingPrimFnSemantics fn)

    M.CLMul x y ->
      do let f = fnClMul (symFuns sym)
             s = symIface sym
         src1 <- toValBV bak x
         src2 <- toValBV bak y
         let ps = extend (extend empty src1) src2
         llvmPointer_bv s =<< applySymFn s f ps

    M.AESNI_AESEnc x y -> pureSemSymBin sym fnAesEnc x y
    M.AESNI_AESEncLast x y -> pureSemSymBin sym fnAesEncLast x y
    M.AESNI_AESDec x y -> pureSemSymBin sym fnAesDec x y
    M.AESNI_AESDecLast x y -> pureSemSymBin sym fnAesDecLast x y
    M.AESNI_AESKeyGenAssist x i ->
      do let f = fnAesKeyGenAssist (symFuns sym)
             s = symIface sym
         src <- toValBV bak x
         roundConst <- bvLit s knownNat $ BV.mkBV knownNat $ fromIntegral i
         let ps = extend (extend empty src) roundConst
         llvmPointer_bv s =<< applySymFn s f ps
    M.AESNI_AESIMC x ->
      do let f = fnAesIMC (symFuns sym)
             s = symIface sym
         src <- toValBV bak x
         let ps = extend empty src
         llvmPointer_bv s =<< applySymFn s f ps

    M.SHA_sigma0 x -> pureSemSymUn sym fnShasigma0 x
    M.SHA_sigma1 x -> pureSemSymUn sym fnShasigma1 x
    M.SHA_Sigma0 x -> pureSemSymUn sym fnShaSigma0 x
    M.SHA_Sigma1 x -> pureSemSymUn sym fnShaSigma1 x
    M.SHA_Ch x y z -> pureSemSymTern sym fnShaCh x y z
    M.SHA_Maj x y z -> pureSemSymTern sym fnShaMaj x y z
    M.X86Syscall {} -> error "X86Syscall should be eliminated and replaced by X86PrimSyscall to look up a function handle"

semPointwise :: (1 <= w) =>
  M.AVXPointWiseOp2 -> NatRepr w ->
    E sym (BVType w) -> E sym (BVType w) -> E sym (BVType w)
semPointwise op w x y =
  case op of
    M.PtAdd -> app (BVAdd w x y)
    M.PtSub -> app (BVSub w x y)
    M.PtCmpGt -> app $ BVIte
      (app (BVSlt w y x))
      w
      (app (BVLit w (BV.mkBV w (-1))))
      (app (BVLit w (BV.mkBV w 0)))

-- | Assumes big-endian split
-- See `vpalign` Intel instruction.
vpalign :: Word8 ->
           V.Vector 16 (E sym (BVType 8)) ->
           V.Vector 16 (E sym (BVType 8)) ->
           V.Vector 16 (E sym (BVType 8))
vpalign i xs ys =
  V.slice n16 n16 (V.shiftR (fromIntegral i) (bv 0) (V.append xs ys))

-- | Shuffling with a mask.
-- See `vpshufd` Intel instruction.
shuffleD :: Word8 -> V.Vector 4 (E sym (BVType 32)) ->
                    V.Vector 4 (E sym (BVType 32))
shuffleD w = V.shuffle getField
  where
  -- Every 2 bits correspond to an index in the input.
  getField x = fromIntegral ((w `shiftR` (2 * x)) .&. 0x03)

-- | See `vpshufb` Intel instruction.
shuffleB :: V.Vector 16 (E sym (BVType 8)) {- ^ Input data -} ->
            V.Vector 16 (E sym (BVType 8)) {- ^ Indexes    -} ->
            V.Vector 16 (E sym (BVType 8))
shuffleB xs is = fmap lkp is
  where
  lkp i = app (BVIte (bvTestBit i 7) knownNat
              (bv 0)
              (bvLookup xs (app $ BVTrunc n4 knownNat i)))

--------------------------------------------------------------------------------

divNatReprClasses :: M.RepValSize w
                  -> (( KnownNat w
                      , 1 <= w
                      , 1 <= w+w
                      , w+1 <= w+w
                      ) => a)
                  -> a
divNatReprClasses r x =
  case r of
    M.ByteRepVal  -> x
    M.WordRepVal  -> x
    M.DWordRepVal -> x
    M.QWordRepVal -> x

-- | Construct a symbolic Macaw pair. Note that @'mkPair' sym x y@ returns the
-- pair @(y, x)@ and /not/ @(x, y)@. This is because Macaw tuples have the order
-- of their fields reversed when converted to a Crucible value (see
-- 'macawListToCrucible' in "Data.Macaw.Symbolic.PersistentState" in
-- @macaw-symbolic@), so we also reverse the order here to be consistent with
-- this convention. (Not doing this can cause serious bugs, such as
-- <https://github.com/GaloisInc/macaw/issues/393>).
mkPair :: forall sym bak x y
       .  (IsSymBackend sym bak, KnownRepr TypeRepr x, KnownRepr TypeRepr y)
       => Sym sym bak
       -> RegValue sym x
       -> RegValue sym y
       -> IO (RegValue sym (StructType (EmptyCtx ::> y ::> x)))
mkPair sym q r = do
  let pairType :: Ctx.Assignment TypeRepr (EmptyCtx ::> y ::> x)
      pairType = Ctx.empty Ctx.:> knownRepr Ctx.:> knownRepr
  let pairRes :: Ctx.Assignment (RegValue' sym) (EmptyCtx ::> y ::> x)
      pairRes = Ctx.empty Ctx.:> RV r Ctx.:> RV q
  evalApp' sym (\v -> pure (unRV v)) $ MkStruct pairType pairRes


-- | Get numerator from pair of Macaw terms
getNumerator :: (IsSymBackend sym bak)
                    => (1 <= w, w+1 <= w+w, 1 <= w+w)
                    => NatRepr w
                    -> Sym sym bak
                    -> AtomWrapper (RegEntry sym) (M.BVType w)
                    -> AtomWrapper (RegEntry sym) (M.BVType w)
                    -> IO (RegValue sym (BVType (w+w)))
getNumerator dw sym macawNum1 macawNum2 = do
  let bak = symBackend sym
  -- Get top half of numerator
  num1 <- getBitVal bak macawNum1
  -- Get bottom half of numerator
  num2 <- getBitVal bak macawNum2
  -- Get bottom half of numerator
  evalApp sym $ BVConcat dw dw num1 num2

-- | Get extended denominator and assert it is not zero.
getDenominator :: (IsSymBackend sym bak)
                    => 1 <= w
                    => NatRepr w
                    -> Sym sym bak
                    -> AtomWrapper (RegEntry sym) (M.BVType w)
                    -> IO (E sym (BVType w))
getDenominator dw sym macawDenom = do
  let bak = symBackend sym
  den <- getBitVal bak macawDenom
  -- Check denominator is not 0
  do let bvZ = app (BVLit dw (BV.zero dw))
     denNotZero <- evalApp sym $ Not (app (BVEq dw den bvZ))
     let errMsg = "denominator not zero"
     assert bak denNotZero (C.AssertFailureSimError errMsg (errMsg ++ " in Data.Macaw.X86.Crucible.getDenominator"))
  pure den

-- | Performs a simple unsigned division operation.
--
-- The x86 numerator is twice the size as the denominator.
--
-- This function is only reponsible for the dividend (not any
-- remainder--see uRem for that), and any divide-by-zero exception was
-- already handled via an Assert.
uDivRem :: forall sym bak w
        .  (IsSymBackend sym bak)
        => Sym sym bak
        -> M.RepValSize w
        -> AtomWrapper (RegEntry sym) (M.BVType w)
        -> AtomWrapper (RegEntry sym) (M.BVType w)
        -> AtomWrapper (RegEntry sym) (M.BVType w)
        -> IO (RegValue sym
                (StructType (EmptyCtx ::> LLVMPointerType w ::> LLVMPointerType w)))
uDivRem sym repsz macawNum1 macawNum2 macawDenom =
  divNatReprClasses repsz $ do
    let dw = M.typeWidth (M.repValSizeMemRepr repsz)
    -- Get natwidth of w+w
    let nw = addNat dw dw
    let symi = symIface sym
    let bak = symBackend sym
    -- Get numerator
    numExt <- getNumerator dw sym macawNum1 macawNum2
    -- Get denominator
    den <- getDenominator dw sym macawDenom
    -- Get extended denominator
    denExt <- evalApp sym $ BVZext nw dw den
    -- Get extended quotient
    qExt <- evalApp sym $ BVUdiv nw (ValBV nw numExt) (ValBV nw denExt)
    -- Get Quotient as bitvector
    qBV <- evalApp sym $ BVTrunc dw nw (ValBV nw qExt)
    -- Check quotient did not overflow.
    do let qExt' = app (BVZext nw dw (ValBV dw qBV))
       qNoOverflow <- evalApp sym $ BVEq nw (ValBV nw qExt) qExt'
       let errMsg = "quotient no overflow"
       assert bak qNoOverflow (C.AssertFailureSimError errMsg (errMsg ++ " in Data.Macaw.X86.Crucible.uDivRem"))
    -- Get quotient
    q <- llvmPointer_bv symi qBV
    -- Get remainder
    r <- do
      let rext = app (BVUrem nw (ValBV nw numExt) (ValBV nw denExt))
      rv <- evalE sym $ app (BVTrunc dw nw rext)
      llvmPointer_bv symi (rv :: RegValue sym (BVType w))
    mkPair sym q r

sDivRem :: forall sym bak w
        .  (IsSymBackend sym bak)
        => Sym sym bak
        -> M.RepValSize w
        -> AtomWrapper (RegEntry sym) (M.BVType w)
        -> AtomWrapper (RegEntry sym) (M.BVType w)
        -> AtomWrapper (RegEntry sym) (M.BVType w)
        -> IO (RegValue sym
                (StructType (EmptyCtx ::> LLVMPointerType w ::> LLVMPointerType w)))
sDivRem sym repsz macawNum1 macawNum2 macawDenom =
  divNatReprClasses repsz $ do
    let dw = M.typeWidth (M.repValSizeMemRepr repsz)
    -- Get natwidth of w+w
    let nw = addNat dw dw
    let bak = symBackend sym
    let symi = symIface sym
    -- Get numerator
    numExt <- getNumerator dw sym macawNum1 macawNum2
    -- Get denominator
    den <- getDenominator dw sym macawDenom
    -- Get extended denominator
    denExt <- evalApp sym $ BVSext nw dw den
    -- Get extended quotient
    qExt <- evalApp sym $ BVSdiv nw (ValBV nw numExt) (ValBV nw denExt)
    -- Get Quotient as bitvector
    qBV <- evalApp sym $ BVTrunc dw nw (ValBV nw qExt)
    -- Check quotient did not overflow.
    do let qExt' = app (BVSext nw dw (ValBV dw qBV))
       qNoOverflow <- evalApp sym $ BVEq nw (ValBV nw qExt) qExt'
       let errMsg = "quotient no overflow"
       assert bak qNoOverflow (C.AssertFailureSimError errMsg (errMsg ++ " in Data.Macaw.X86.Crucible.sDivRem"))
    -- Get quotient
    q <- llvmPointer_bv symi qBV
    -- Get remainder
    r <- do
      let rext = app (BVSrem nw (ValBV nw numExt) (ValBV nw denExt))
      rv <- evalE sym $ app (BVTrunc dw nw rext)
      llvmPointer_bv symi (rv :: RegValue sym (BVType w))
    mkPair sym q r

--------------------------------------------------------------------------------
divExact ::
  NatRepr n ->
  NatRepr x ->
  (forall i. ((i * x) ~ n, 1 <= i) => NatRepr i -> k) ->
  k
divExact n x k = withDivModNat n x $ \i r ->
  case testEquality r n0 of
    Just Refl ->
      case testLeq n1 i of
        Just LeqProof -> k i
        Nothing       -> error "divExact: 0 input"
    Nothing -> error "divExact: not a multiple of 16"


vecOp1 :: (IsSymBackend sym bak, 1 <= c) =>
  Sym sym bak {- ^ Simulator -} ->
  Endian      {- ^ How to split-up the bit-vector -} ->
  NatRepr w   {- ^ Total width of the bit-vector -} ->
  NatRepr c   {- ^ Width of individual elements -} ->
  AtomWrapper (RegEntry sym) (M.BVType w) {- ^ The input value -} ->
  (forall n. (1 <= n, (n * c) ~ w) =>
     V.Vector n (E sym (BVType c)) -> V.Vector n (E sym (BVType c)))
  {- ^ Definition of operation -} ->
  IO (RegValue sym (LLVMPointerType w)) -- ^ The final result.
vecOp1 sym endian totLen elLen x f =
  unpack (symBackend sym) endian totLen elLen x $ \v ->
  llvmPointer_bv (symIface sym) =<< evalE sym (V.toBV endian elLen (f v))


vecOp2 :: (IsSymBackend sym bak, 1 <= c) =>
  Sym sym bak {- ^ Simulator -} ->
  Endian      {- ^ How to split-up the bit-vector -} ->
  NatRepr w   {- ^ Total width of the bit-vector -} ->
  NatRepr c   {- ^ Width of individual elements -} ->
  AtomWrapper (RegEntry sym) (M.BVType w) {- ^ Input value 1 -} ->
  AtomWrapper (RegEntry sym) (M.BVType w) {- ^ Input value 2 -} ->
  (forall n. (1 <= n, (n * c) ~ w) =>
     V.Vector n (E sym (BVType c)) ->
     V.Vector n (E sym (BVType c)) ->
     V.Vector n (E sym (BVType c))) {- ^ Definition of operation -} ->
  IO (RegValue sym (LLVMPointerType w)) -- ^ The final result.
vecOp2 sym endian totLen elLen x y f =
  unpack2 (symBackend sym) endian totLen elLen x y $ \u v ->
  llvmPointer_bv (symIface sym) =<< evalE sym (V.toBV endian elLen (f u v))

bitOp2 :: (IsSymBackend sym bak) =>
  Sym sym bak                             {- ^ The simulator -} ->
  AtomWrapper (RegEntry sym) (M.BVType w) {- ^ Input 1 -} ->
  AtomWrapper (RegEntry sym) (M.BVType w) {- ^ Input 2 -} ->
  (E sym (BVType w) -> E sym (BVType w) -> App () (E sym) (BVType w))
                                          {- ^ The definition of the operation -} ->
  IO (RegValue sym (LLVMPointerType w))   {- ^ The result -}
bitOp2 sym x y f =
  do let bak = symBackend sym
     x' <- getBitVal bak x
     y' <- getBitVal bak y
     llvmPointer_bv (symIface sym) =<< evalE sym (app (f x' y'))


-- | Split up a bit-vector into a vector.
-- Even though X86 is little endian for memory accesses, this function
-- is parameterized by endianness, as some instructions are more naturally
-- expressed by splitting big-endian-wise (e.g., shifts)
unpack ::
  (1 <= c, IsSymBackend sym bak) =>
  bak ->
  Endian ->
  NatRepr w                               {- ^ Original length -} ->
  NatRepr c                               {- ^ Size of each chunk -} ->
  AtomWrapper (RegEntry sym) (M.BVType w) {- ^ Input value -} ->
  (forall n. (1 <= n, (n * c) ~ w) => V.Vector n (E sym (BVType c)) -> IO a) ->
  IO a
unpack bak e w c v k = divExact w c $ \n ->
  do b <- getBitVal bak v
     k (V.fromBV e n c b)

-- | Split up two bit-vectors into sub-chunks.
unpack2 ::
  (1 <= c, IsSymBackend sym bak) =>
  bak ->
  Endian ->
  NatRepr w ->
  NatRepr c ->
  AtomWrapper (RegEntry sym) (M.BVType w) ->
  AtomWrapper (RegEntry sym) (M.BVType w) ->
  (forall n. (1 <= n, (n * c) ~ w) =>
      V.Vector n (E sym (BVType c)) ->
      V.Vector n (E sym (BVType c)) ->
      IO a) ->
  IO a
unpack2 bak e w c v1 v2 k =
  divExact w c $ \n ->
    do v1' <- getBitVal bak v1
       v2' <- getBitVal bak v2
       k (V.fromBV e n c v1') (V.fromBV e n c v2')

-- | Extract the offset from an LLVMPointer
--
-- Note that this version generates an /assertion/ that the block number is
-- zero, and should be used carefully. See 'getPointerOffset' for a variant that
-- does not generate proof obligations.
--
-- XXX: Do we want to be strict here (i.e., asserting that the thing is
-- not a pointer, or should be lenent, i.e., return an undefined value?)
getBitVal ::
  (IsSymBackend sym bak) =>
  bak ->
  AtomWrapper (RegEntry sym) (M.BVType w) ->
  IO (E sym (BVType w))
getBitVal bak (AtomWrapper x) =
  do v <- projectLLVM_bv bak (regValue x)
     case regType x of
       LLVMPointerRepr w -> return (ValBV w v)
       _ -> error "getBitVal: impossible"

-- | Extract the offset from an LLVMPointer without checking whether or not the
-- block number is zero
getPointerOffset ::
  AtomWrapper (RegEntry sym) (M.BVType w) ->
  IO (E sym (BVType w))
getPointerOffset (AtomWrapper x) =
  case regType x of
    LLVMPointerRepr w -> return (ValBV w (Pointer.llvmPointerOffset (regValue x)))
    tp -> error ("getPointerOffset: unexpected type repr " ++ show tp)

toValBV ::
  (IsSymBackend sym bak) =>
  bak ->
  AtomWrapper (RegEntry sym) (M.BVType w) ->
  IO (RegValue sym (BVType w))
toValBV bak (AtomWrapper x) = projectLLVM_bv bak (regValue x)

floatInfoFromSSEType
  :: M.SSE_FloatType tp -> FloatInfoRepr (ToCrucibleFloatInfo tp)
floatInfoFromSSEType = \case
  M.SSE_Single -> knownRepr
  M.SSE_Double -> knownRepr

--------------------------------------------------------------------------------
-- A small functor that allows mixing of values and Crucible expressions.

data E :: Type -> CrucibleType -> Type where
  ValBool :: RegValue sym BoolType -> E sym BoolType
  ValBV :: (1 <= w) => NatRepr w -> RegValue sym (BVType w) -> E sym (BVType w)
  Expr :: App () (E sym) t -> E sym t

instance IsExpr (E sym) where
  type ExprExt (E sym) = ()
  app = Expr
  asApp e = case e of
              Expr a -> Just a
              _      -> Nothing
  exprType e = case e of
                Expr a -> appType a
                ValBool _  -> knownRepr
                ValBV n _  -> BVRepr n

evalE :: (IsSymBackend sym bak) =>
  Sym sym bak -> E sym t -> IO (RegValue sym t)
evalE sym e = case e of
                ValBool x -> return x
                ValBV _ x -> return x
                Expr a    -> evalApp sym a

evalApp :: forall sym bak t. (IsSymBackend sym bak) =>
         Sym sym bak -> App () (E sym) t -> IO (RegValue sym t)
evalApp sym = evalApp' sym (evalE sym)

bv :: (KnownNat w, 1 <= w) => Int -> E sym (BVType w)
bv i = app (BVLit knownNat (BV.mkBV knownNat (toInteger i)))

bvTestBit :: (KnownNat w, 1 <= w) => E sym (BVType w) -> Int -> E sym BoolType
bvTestBit e n = app $ BVNonzero knownNat $
                app $ BVAnd knownNat e (bv (shiftL 1 n))


bvLookup ::
  (1 <= w, KnownNat w) =>
  V.Vector 16 (E sym (BVType w)) ->
  E sym (BVType 4) ->
  E sym (BVType w)
bvLookup xs ind = ite 0 3
  where
  ite i b = if b < 0
                then V.elemAtUnsafe i xs
                else app $ BVIte (bvTestBit ind b) knownNat
                                 (ite (2 * i + 1) (b - 1))
                                 (ite (2 * i)     (b - 1))

bvShiftL :: (1 <= w, 1 <= i) =>
  NatRepr w -> NatRepr i ->
  E sym (BVType w) -> E sym (BVType i) -> E sym (BVType w)
bvShiftL w i vw vi = app (BVShl w vw amt)
  where amt = case testNatCases i w of
                NatCaseEQ -> vi
                NatCaseLT LeqProof -> app (BVZext w i vi)
                NatCaseGT LeqProof -> app (BVTrunc w i vi)

bvLogicalShiftR :: (1 <= w, 1 <= i) =>
  NatRepr w -> NatRepr i ->
  E sym (BVType w) -> E sym (BVType i) -> E sym (BVType w)
bvLogicalShiftR w i vw vi = app (BVLshr w vw amt)
  where amt = case testNatCases i w of
                NatCaseEQ -> vi
                NatCaseLT LeqProof -> app (BVZext w i vi)
                NatCaseGT LeqProof -> app (BVTrunc w i vi)


--------------------------------------------------------------------------------

n0 :: NatRepr 0
n0 = knownNat

n1 :: NatRepr 1
n1 = knownNat

n2 :: NatRepr 2
n2 = knownNat

n4 :: NatRepr 4
n4 = knownNat

n8 :: NatRepr 8
n8 = knownNat

n16 :: NatRepr 16
n16 = knownNat

n32 :: NatRepr 32
n32 = knownNat

n64 :: NatRepr 64
n64 = knownNat

n128 :: NatRepr 128
n128 = knownNat

--------------------------------------------------------------------------------

newtype AtomWrapper (f :: CrucibleType -> Type) (tp :: M.Type)
  = AtomWrapper (f (ToCrucibleType tp))

liftAtomMap :: (forall s. f s -> g s) -> AtomWrapper f t -> AtomWrapper g t
liftAtomMap f (AtomWrapper x) = AtomWrapper (f x)

liftAtomTrav ::
  Functor m =>
  (forall s. f s -> m (g s)) -> (AtomWrapper f t -> m (AtomWrapper g t))
liftAtomTrav f (AtomWrapper x) = AtomWrapper <$> f x

liftAtomIn :: (forall s. f s -> a) -> AtomWrapper f t -> a
liftAtomIn f (AtomWrapper x) = f x

{- Note [EvenParity Semantics]

Originally, the implementation of the semantics of 'EvenParity' used
'getBitVal'. This worked up until 'PtrAdd' was generalized to not be restricted
to pointer-width operands. In turn, that change was motivated by some
architectures extending pointers for certain operations. The previous
implementation meant that extending pointers threw away their block number and
treated them as bitvectors forever after.

With that change, the pattern around 'EvenParity' in x86 broke:

> %1 = trunc ptr 8
> %2 = even_parity %1

Note that in the original semantics, the truncation drops the block number
unconditionally, which meant that applying llvmPointer_bv (in 'getBitVal') was
fine: it produced a trivial proof obligation that the block number was zero
(assert 0 == 0).

However, after the generalization, the block number was preserved (and
concretely not zero), so the generated proof obligation now failed.  The new
implementation uses 'getPointerOffset', which extracts the offset without
generating any side conditions.

Is this safe? The original implementation implied that testing the parity of a
pointer is unsafe because we don't formally know what the address is, so the
question doesn't really make sense. We also don't know the alignment of the
underlying allocation (if we did, we could compute the parity given the
offset). Technically that is true, but even if we wanted to enforce that, the
original implementation was not correct: the truncation unconditionally
discarded the block number. The current implementation (using
'getPointerOffset') is as safe as the original. In both cases, we essentially
require that all allocations are aligned to at least a two byte boundary.

See macaw#260 for the relevant discussion (summarized here).

-}
