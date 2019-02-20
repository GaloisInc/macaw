{-|
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines operations for mapping flexdis values to Macaw values.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.X86.Getters
  ( SomeBV(..)
  , getBVAddress
  , readBVAddress
  , getSomeBVLocation
  , getBVLocation
  , getSomeBVValue
  , getBVValue
  , getSignExtendedValue
  , truncateBVValue
  , getCallTarget
  , doJump
  , HasRepSize(..)
  , getAddrRegOrSegment
  , getAddrRegSegmentOrImm
  , readXMMValue
  , readYMMValue
  , getImm32
    -- * Utilities
  , reg8Loc
  , reg16Loc
  , reg32Loc
  , reg64Loc
  , getBV8Addr
  , getBV16Addr
  , getBV32Addr
  , getBV64Addr
  , getBV80Addr
  , getBV128Addr
    -- * Reprs
  , byteMemRepr
  , wordMemRepr
  , dwordMemRepr
  , qwordMemRepr
  , x87MemRepr
  , xmmMemRepr
  , ymmMemRepr
  ) where

import           Control.Lens ((&))
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Some
import qualified Data.Text as T
import qualified Flexdis86 as F
import           GHC.TypeLits (KnownNat)

import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block ( TermStmt(TranslateError) )
import           Data.Macaw.Types
import           Data.Macaw.X86.Generator
import           Data.Macaw.X86.Monad
import           Data.Macaw.X86.X86Reg (X86Reg(..))

type BVExpr ids w = Expr ids (BVType w)
type Addr s = Expr s (BVType 64)

byteMemRepr :: MemRepr (BVType 8)
byteMemRepr = BVMemRepr (knownNat :: NatRepr 1) LittleEndian

wordMemRepr :: MemRepr (BVType 16)
wordMemRepr = BVMemRepr (knownNat :: NatRepr 2) LittleEndian

dwordMemRepr :: MemRepr (BVType 32)
dwordMemRepr = BVMemRepr (knownNat :: NatRepr 4) LittleEndian

qwordMemRepr :: MemRepr (BVType 64)
qwordMemRepr = BVMemRepr (knownNat :: NatRepr 8) LittleEndian

x87MemRepr :: MemRepr (BVType 80)
x87MemRepr = BVMemRepr (knownNat :: NatRepr 10) LittleEndian

xmmMemRepr :: MemRepr (BVType 128)
xmmMemRepr = BVMemRepr (knownNat :: NatRepr 16) LittleEndian

ymmMemRepr :: MemRepr (BVType 256)
ymmMemRepr = BVMemRepr (knownNat :: NatRepr 32) LittleEndian

------------------------------------------------------------------------
-- Utilities

-- | Return a location from a 16-bit register
reg8Loc :: F.Reg8 -> Location addr (BVType 8)
reg8Loc (F.LowReg8 r)  = reg_low8  $ X86_GP $ F.Reg64 r
reg8Loc (F.HighReg8 r) = reg_high8 $ X86_GP $ F.Reg64 r
reg8Loc _ = error "internal: Unepxected byteReg"

-- | Return a location from a 16-bit register
reg16Loc :: F.Reg16 -> Location addr (BVType 16)
reg16Loc = reg_low16 . X86_GP . F.reg16_reg

-- | Return a location from a 32-bit register
reg32Loc :: F.Reg32 -> Location addr (BVType 32)
reg32Loc = reg_low32 . X86_GP . F.reg32_reg

-- | Return a location from a 64-bit register
reg64Loc :: F.Reg64 -> Location addr (BVType 64)
reg64Loc = fullRegister . X86_GP

------------------------------------------------------------------------
-- Getters

getImm32 :: F.Imm32 -> BVExpr ids 32
getImm32 (F.Imm32Concrete w) = bvLit n32 (toInteger w)
getImm32 (F.Imm32SymbolOffset sym off _) =
  bvTrunc' n32 (ValueExpr (SymbolValue Addr64 sym))
  .+ bvLit n32 (toInteger off)

-- | Return the value of a 32-bit displacement.
getDisplacement32 :: F.Displacement -> BVExpr ids 32
getDisplacement32 F.NoDisplacement = bvLit n32 0
getDisplacement32 (F.Disp8 x) = bvLit n32 (toInteger x)
getDisplacement32 (F.Disp32 x) =  getImm32 x

-- | Return the value of a 32-bit displacement.
getDisplacement64 :: F.Displacement -> BVExpr ids 64
getDisplacement64 F.NoDisplacement = bvLit n64 0
getDisplacement64 (F.Disp8 x)      = bvLit n64 (toInteger x)
getDisplacement64 (F.Disp32 (F.Imm32Concrete x)) = bvLit n64 (toInteger x)
getDisplacement64 (F.Disp32 (F.Imm32SymbolOffset sym off _)) =
  ValueExpr (SymbolValue Addr64 sym)
    .+ bvLit n64 (toInteger off)

-- | Calculates the address corresponding to an AddrRef
getBVAddress :: F.AddrRef -> X86Generator st ids (BVExpr ids 64)
getBVAddress ar =
  case ar of
   -- FIXME: It seems that there is no sign extension here ...
    F.Addr_32 seg m_r32 m_int_r32 i32 -> do
      base <- case m_r32 of
                Nothing -> return $! bvKLit 0
                Just r  -> get (reg32Loc r)
      scale <-
        case m_int_r32 of
          Nothing     -> return $! bvKLit 0
          Just (i, r) ->
            bvTrunc n32 . (bvLit n32 (toInteger i) .*)
              <$> get (reg32Loc r)

      let offset = uext n64 (base .+ scale .+ getDisplacement32 i32)
      mk_absolute seg offset
    F.IP_Offset_32 _seg _i32 -> fail "IP_Offset_32"
    F.Offset_32    _seg _w32 ->
      fail "Offset_32"
    F.Offset_64 seg w64 -> do
      mk_absolute seg (bvLit n64 (toInteger w64))
    F.Addr_64 seg m_r64 m_int_r64 disp -> do
      base <- case m_r64 of
                Nothing -> return v0_64
                Just r  -> get (reg64Loc r)
      scale <-
        case m_int_r64 of
          Nothing     -> return v0_64
          Just (i, r) ->
            bvTrunc n64 . (bvLit n64 (toInteger i) .*) <$> get (reg64Loc r)
      let offset = base .+ scale .+ getDisplacement64 disp
      mk_absolute seg offset
    F.IP_Offset_64 seg disp -> do
      ipVal <- get rip
      mk_absolute seg (ipVal .+ getDisplacement64 disp)
  where
    v0_64 = bvLit n64 0
    -- | Add the segment base to compute an absolute address.
    mk_absolute :: F.Segment -> Addr ids -> X86Generator st ids (Expr ids (BVType 64))
    mk_absolute seg offset
      -- In 64-bit mode the CS, DS, ES, and SS segment registers
      -- are forced to zero, and so segmentation is a nop.
      --
      -- We could nevertheless call 'getSegmentBase' in all cases
      -- here, but that adds a lot of noise to the AST in the common
      -- case of segments other than FS or GS.
      | seg == F.CS || seg == F.DS || seg == F.ES || seg == F.SS =
        return offset
      -- The FS and GS segments can be non-zero based in 64-bit mode.
      | otherwise = do
        base <- getSegmentBase seg
        return $ base .+ offset

-- | Translate a flexdis address-refrence into a one-byte address.
getBV8Addr :: F.AddrRef -> X86Generator st ids (Location (Addr ids) (BVType 8))
getBV8Addr ar = (`MemoryAddr`  byteMemRepr) <$> getBVAddress ar

-- | Translate a flexdis address-refrence into a two-byte address.
getBV16Addr :: F.AddrRef -> X86Generator st ids (Location (Addr ids) (BVType 16))
getBV16Addr ar = (`MemoryAddr`  wordMemRepr) <$> getBVAddress ar

-- | Translate a flexdis address-refrence into a four-byte address.
getBV32Addr :: F.AddrRef -> X86Generator st ids (Location (Addr ids) (BVType 32))
getBV32Addr ar = (`MemoryAddr` dwordMemRepr) <$> getBVAddress ar

-- | Translate a flexdis address-refrence into a eight-byte address.
getBV64Addr :: F.AddrRef -> X86Generator st ids (Location (Addr ids) (BVType 64))
getBV64Addr ar = (`MemoryAddr` qwordMemRepr) <$> getBVAddress ar

-- | Translate a flexdis address-refrence into a ten-byte address.
getBV80Addr :: F.AddrRef -> X86Generator st ids (Location (Addr ids) (BVType 80))
getBV80Addr ar = (`MemoryAddr` x87MemRepr) <$> getBVAddress ar

-- | Translate a flexdis address-refrence into a sixteen-byte address.
getBV128Addr :: F.AddrRef -> X86Generator st ids (Location (Addr ids) (BVType 128))
getBV128Addr ar = (`MemoryAddr` xmmMemRepr) <$> getBVAddress ar

-- | Translate a flexdis address-refrence into a sixteen-byte address.
getBV256Addr :: F.AddrRef -> X86Generator st ids (Location (Addr ids) (BVType 256))
getBV256Addr ar = (`MemoryAddr` ymmMemRepr) <$> getBVAddress ar

readBVAddress :: F.AddrRef -> MemRepr tp -> X86Generator st ids (Expr ids tp)
readBVAddress ar repr = get . (`MemoryAddr` repr) =<< getBVAddress ar

-- | A bitvector value with a width that satisfies `SupportedBVWidth`.
data SomeBV v where
  SomeBV :: SupportedBVWidth n => v (BVType n) -> SomeBV v



-- | Extract the location of a bitvector value.
getSomeBVLocation :: F.Value -> X86Generator st ids (SomeBV (Location (Addr ids)))
getSomeBVLocation v =
  case v of
    F.ControlReg cr  -> pure $ SomeBV $ ControlReg cr
    F.DebugReg dr    -> pure $ SomeBV $ DebugReg dr
    F.MMXReg mmx     -> pure $ SomeBV $ x87reg_mmx $ X87_FPUReg mmx
    F.XMMReg r       -> do avx <- isAVX
                           pure $ SomeBV $ if avx then xmm_avx r
                                                  else xmm_sse r
    F.YMMReg r       -> do avx <- isAVX
                           pure $ SomeBV $ if avx then ymm_zero r else ymm_preserve r
    F.SegmentValue s -> pure $ SomeBV $ SegmentReg s
    F.X87Register i -> mk (X87StackRegister i)
    F.FarPointer _      -> fail "FarPointer"
    -- SomeBV . (`MemoryAddr`   byteMemRepr) <$> getBVAddress ar -- FIXME: what size here?
    F.VoidMem _  -> fail "VoidMem"
    F.Mem8   ar  -> SomeBV <$> getBV8Addr   ar
    F.Mem16  ar  -> SomeBV <$> getBV16Addr  ar
    F.Mem32  ar  -> SomeBV <$> getBV32Addr  ar
    F.Mem64  ar  -> SomeBV <$> getBV64Addr  ar
    F.Mem128 ar  -> SomeBV <$> getBV128Addr ar
    F.Mem256 ar  -> SomeBV <$> getBV256Addr ar
    F.FPMem32 ar -> getBVAddress ar >>= mk . (`MemoryAddr` (floatMemRepr SingleFloatRepr))
    F.FPMem64 ar -> getBVAddress ar >>= mk . (`MemoryAddr` (floatMemRepr DoubleFloatRepr))
    F.FPMem80 ar -> getBVAddress ar >>= mk . (`MemoryAddr` (floatMemRepr X86_80FloatRepr))
    F.ByteReg  r -> mk $ reg8Loc  r
    F.WordReg  r -> mk $ reg16Loc r
    F.DWordReg r -> mk $ reg32Loc r
    F.QWordReg r -> mk $ reg64Loc r
    F.ByteImm  _ -> noImm
    F.WordImm  _ -> noImm
    F.DWordImm _ -> noImm
    F.QWordImm _ -> noImm
    F.ByteSignedImm  _ -> noImm
    F.WordSignedImm  _ -> noImm
    F.DWordSignedImm _ -> noImm
    F.JumpOffset{}  -> fail "Jump Offset is not a location."
  where
    noImm :: Monad m => m a
    noImm = fail "Immediate is not a location"
    mk :: (Applicative m, SupportedBVWidth n) => f (BVType n) -> m (SomeBV f)
    mk = pure . SomeBV

-- | Translate a flexdis value to a location with a particular width.
getBVLocation :: F.Value -> NatRepr n -> X86Generator st ids (Location (Addr ids) (BVType n))
getBVLocation l expected = do
  SomeBV v <- getSomeBVLocation l
  case testEquality (typeWidth v) expected of
    Just Refl ->
      return v
    Nothing ->
      fail $ "Widths aren't equal: " ++ show (typeWidth v) ++ " and " ++ show expected

-- | Return a bitvector value.
getSomeBVValue :: F.Value -> X86Generator st ids (SomeBV (Expr ids))
getSomeBVValue v =
  case v of
    F.ByteImm  w      -> pure $! SomeBV $ bvLit n8  $ toInteger w
    F.ByteSignedImm w -> pure $! SomeBV $ bvLit n8  $ toInteger w
    F.WordImm  w      -> pure $! SomeBV $ bvLit n16 $ toInteger w
    F.WordSignedImm w -> pure $! SomeBV $ bvLit n16 $ toInteger w
    F.DWordImm i      -> pure $! SomeBV $ getImm32 i
    F.DWordSignedImm w -> pure $! SomeBV $ bvLit n32 $ toInteger w
    F.QWordImm w      -> pure $! SomeBV $ bvLit n64 $ toInteger w
    F.JumpOffset _ _  -> fail "Jump Offset should not be treated as a BVValue."
    _ -> do
      SomeBV l <- getSomeBVLocation v
      SomeBV <$> get l

-- | Translate a flexdis value to a value with a particular width.
getBVValue :: F.Value
           -> NatRepr n
           -> X86Generator st ids (Expr ids (BVType n))
getBVValue val expected = do
  SomeBV v <- getSomeBVValue val
  case testEquality (typeWidth v) expected of
    Just Refl -> return v
    Nothing ->
      fail $ "Widths aren't equal: " ++ show (typeWidth v) ++ " and " ++ show expected

-- | Get a value with the given width, sign extending as necessary.
getSignExtendedValue :: forall st ids w
                     .  1 <= w
                     => F.Value
                     -> NatRepr w
                     -> X86Generator st ids (Expr ids (BVType w))
getSignExtendedValue v out_w =
  case v of
    -- If an instruction can take a VoidMem, it needs to get it explicitly
    F.VoidMem _ar -> fail "VoidMem"
    F.Mem8   ar   -> mk =<< getBV8Addr ar
    F.Mem16  ar   -> mk =<< getBV16Addr ar
    F.Mem32  ar   -> mk =<< getBV32Addr ar
    F.Mem64  ar   -> mk =<< getBV64Addr ar
    F.Mem128 ar   -> mk =<< getBV128Addr ar
    F.Mem256 ar   -> mk =<< getBV256Addr ar
    F.XMMReg r  -> mk (xmm_avx r)
    F.YMMReg r  -> mk (ymm_zero r)

    F.ByteImm  i
      | Just Refl <- testEquality n8 out_w ->
        pure $! bvLit n8 (toInteger i)
    F.WordImm  i
      | Just Refl <- testEquality n16 out_w ->
        pure $! bvLit n16 (toInteger i)
    F.DWordImm (F.Imm32Concrete i)
      | Just Refl <- testEquality n32 out_w ->
        pure $! bvLit n32 (toInteger i)
    F.QWordImm i
      | Just Refl <- testEquality n64 out_w ->
        pure $! bvLit n64 (toInteger i)

    F.ByteSignedImm  i -> pure $! bvLit out_w (toInteger i)
    F.WordSignedImm  i -> pure $! bvLit out_w (toInteger i)
    F.DWordSignedImm i -> pure $! bvLit out_w (toInteger i)

    F.ByteReg  r -> mk $ reg8Loc  r
    F.WordReg  r -> mk $ reg16Loc r
    F.DWordReg r -> mk $ reg32Loc r
    F.QWordReg r -> mk $ reg64Loc r

    _ -> fail $ "getSignExtendedValue given unexpected width: " ++ show v
  where
    -- FIXME: what happens with signs etc?
    mk :: forall u
       .  (1 <= u, KnownNat u)
       => Location (Addr ids) (BVType u)
       -> X86Generator st ids (BVExpr ids w)
    mk l
      | Just LeqProof <- testLeq (knownNat :: NatRepr u) out_w =
        sext out_w <$> get l
      | otherwise =
        fail $ "getSignExtendedValue given bad value."

truncateBVValue :: (Monad m, 1 <= n)
                => NatRepr n
                -> SomeBV (Expr ids)
                -> m (Expr ids (BVType n))
truncateBVValue n (SomeBV v)
  | Just LeqProof <- testLeq n (typeWidth v) = do
      return (bvTrunc n v)
  | otherwise =
    fail $ "Widths isn't >=: " ++ show (typeWidth v) ++ " and " ++ show n

-- | Resolve the address we jump to in the current program.
resolveJumpOffset :: GenState st_s ids
                  -> F.JumpOffset
                  -> BVExpr ids 64
resolveJumpOffset s (F.FixedOffset off) =
  ValueExpr $ RelocatableValue Addr64 $
     segoffAddr (genInitPCAddr s)
     & incAddr (toInteger (genInstructionSize s) + toInteger off)
resolveJumpOffset s (F.RelativeOffset insOff symId off)
  = ValueExpr (SymbolValue Addr64 symId)
  -- We add the offset and the offset within the instruction of this offset,
    -- but have to subtract the current IP
  .+ bvLit n64 (toInteger off + toInteger (genInstructionSize s) - toInteger insOff)

-- | Return the target of a call or jump instruction.
getCallTarget :: F.Value
              -> X86Generator st ids (BVExpr ids 64)
getCallTarget v =
  case v of
    F.Mem64 ar -> get =<< getBV64Addr ar
    F.QWordReg r -> get (reg64Loc r)
    F.JumpOffset _ joff -> do
      s <- getState
      pure $! resolveJumpOffset s joff
    _ -> do
      ipVal <- eval =<< get rip
      let msg = "Data.Macaw.X86.Getters.getCallTarget: Unexpected argument: " ++ show v ++ " at " ++ show ipVal
      addTermStmt (\regs -> TranslateError regs (T.pack msg))

-- | Return the target of a call or jump instruction.
doJump :: Expr ids BoolType -> F.Value -> X86Generator st ids ()
doJump cond v =
  case v of
    F.JumpOffset _ joff -> do
      s <- getState
      modify rip $ mux cond (resolveJumpOffset s joff)
    F.QWordReg r -> do
      ipVal <- get (reg64Loc r)
      modify rip $ mux cond ipVal
    F.Mem64 ar -> do
      condVal <- eval cond
      -- Address to read jump target from
      ipAddr <- eval =<< getBVAddress ar
      -- Get exiting ip value if we need it.
      oldIpVal <- eval =<< get rip
      -- Read the new memory if cond is true, and otherwise return old value.
      ipVal <- evalAssignRhs $ CondReadMem qwordMemRepr condVal ipAddr oldIpVal
      -- Set the ip value.
      rip .= ipVal
    F.QWordImm w -> do
      modify rip $ mux cond $ bvKLit (toInteger w)
    _ -> do
      ipVal <- eval =<< get rip
      let msg = "Data.Macaw.X86.Getters.doJump: Unexpected argument: " ++ show v ++ " at " ++ show ipVal
      addTermStmt (\regs -> TranslateError regs (T.pack msg))

------------------------------------------------------------------------
-- Standard memory values

data HasRepSize f w = HasRepSize { _ppvWidth :: !(RepValSize w)
                                 , _ppvValue :: !(f (BVType w))
                                 }

-- | Gets the location to store the value poped from.
-- These functions only support general purpose registers/addresses and segments.
getAddrRegOrSegment :: F.Value -> X86Generator st ids (Some (HasRepSize (Location (Addr ids))))
getAddrRegOrSegment v =
  case v of
    F.SegmentValue s -> pure $ Some $ HasRepSize WordRepVal (SegmentReg s)
    F.Mem8  ar -> Some . HasRepSize  ByteRepVal <$> getBV8Addr  ar
    F.Mem16 ar -> Some . HasRepSize  WordRepVal <$> getBV16Addr ar
    F.Mem32 ar -> Some . HasRepSize DWordRepVal <$> getBV32Addr ar
    F.Mem64 ar -> Some . HasRepSize QWordRepVal <$> getBV64Addr ar

    F.ByteReg  r -> pure $ Some $ HasRepSize  ByteRepVal $ reg8Loc  r
    F.WordReg  r -> pure $ Some $ HasRepSize  WordRepVal $ reg16Loc r
    F.DWordReg r -> pure $ Some $ HasRepSize DWordRepVal $ reg32Loc r
    F.QWordReg r -> pure $ Some $ HasRepSize QWordRepVal $ reg64Loc r
    _  -> fail $ "Argument " ++ show v ++ " not supported."

-- | Gets a value that can be pushed.
-- These functions only support general purpose registers/addresses and segments.
getAddrRegSegmentOrImm :: F.Value -> X86Generator st ids (Some (HasRepSize (Expr ids)))
getAddrRegSegmentOrImm v =
  case v of
    F.ByteImm  w -> pure $ Some $ HasRepSize ByteRepVal  $ bvLit n8  (toInteger w)
    F.WordImm  w -> pure $ Some $ HasRepSize WordRepVal  $ bvLit n16 (toInteger w)
    F.DWordImm i -> pure $ Some $ HasRepSize DWordRepVal $ getImm32 i
    F.QWordImm w -> pure $ Some $ HasRepSize QWordRepVal $ bvLit n64 (toInteger w)
    F.ByteSignedImm w -> pure $ Some $ HasRepSize ByteRepVal $ bvLit n8 (toInteger w)
    F.WordSignedImm w -> pure $ Some $ HasRepSize WordRepVal $ bvLit n16 (toInteger w)
    F.DWordSignedImm w -> pure $ Some $ HasRepSize DWordRepVal $ bvLit n32 (toInteger w)
    _ -> do
      Some (HasRepSize rep l) <- getAddrRegOrSegment v
      Some . HasRepSize rep <$> get l

------------------------------------------------------------------------
-- SSE

-- | Get a XMM value
readXMMValue :: F.Value -> X86Generator st ids (Expr ids (BVType 128))
readXMMValue (F.XMMReg r) = get (xmm_avx r)
readXMMValue (F.Mem128 a) = readBVAddress a xmmMemRepr
readXMMValue _ = fail "XMM Instruction given unexpected value."

-- | Get a YMM value
readYMMValue :: F.Value -> X86Generator st ids (Expr ids (BVType 256))
readYMMValue (F.YMMReg r) = get (ymm_zero r)
readYMMValue (F.Mem256 a) = readBVAddress a ymmMemRepr
readYMMValue _ = fail "YMM Instruction given unexpected value."
