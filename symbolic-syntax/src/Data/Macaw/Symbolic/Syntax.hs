{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ImplicitParams #-}
{-# LANGUAGE NamedFieldPuns #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}

-- | 'LCSC.ParserHooks' for parsing macaw-symbolic CFGs. Originally ported from:
--
-- https://github.com/GaloisInc/ambient-verifier/blob/eab04abb9750825a25ec0cbe0379add63f05f6c6/src/Ambient/FunctionOverride/Extension.hs#L863
module Data.Macaw.Symbolic.Syntax (
    ExtensionParser
  , SomeExtensionWrapper(..)
  , extensionParser
  , machineCodeParserHooks
  ) where

import Prelude

import           Control.Applicative ( Alternative((<|>), empty) )
import           Control.Monad.IO.Class ( MonadIO(..) )
import           Control.Monad.State.Class ( MonadState )
import           Control.Monad.Writer.Class ( MonadWriter )
import qualified Data.Map.Strict as Map
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.NatRepr as PN
import           Data.Parameterized.Some ( Some(..) )
import           Data.Proxy ( Proxy(..) )
import           GHC.TypeNats ( KnownNat, type (<=), type (+) )
import           Numeric.Natural ( Natural )

import qualified Data.Macaw.CFG as DMC
import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Symbolic as DMS
import qualified Data.Macaw.Types as DMT
import qualified Lang.Crucible.CFG.Expr as LCE
import qualified Lang.Crucible.CFG.Extension as LCCE
import qualified Lang.Crucible.CFG.Reg as LCCR
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified Lang.Crucible.Syntax.Atoms as LCSA
import qualified Lang.Crucible.Syntax.Concrete as LCSC
import qualified Lang.Crucible.Syntax.Monad as LCSM
import qualified Lang.Crucible.Types as LCT
import qualified Lang.Crucible.LLVM.Syntax as LCLS

import qualified What4.Interface as WI
import qualified What4.ProgramLoc as WP

-- | The constraints on the abstract parser monad
type ExtensionParser m ext s = ( LCSM.MonadSyntax LCSA.Atomic m
                               , MonadWriter [WP.Posd (LCCR.Stmt ext s)] m
                               , MonadState (LCSC.SyntaxState s) m
                               , MonadIO m
                               , LCCE.IsSyntaxExtension ext
                               )

-- | A wrapper for a syntax extension statement
--
-- Note that these are pure and are intended to guide the substitution of syntax
-- extensions for operations in the 'MDS.MacawExt' syntax.
data ExtensionWrapper arch args ret =
  ExtensionWrapper { extArgTypes :: LCT.CtxRepr args
                  -- ^ Types of the arguments to the syntax extension
                   , extWrapper :: forall s m
                                 . ( ExtensionParser m (DMS.MacawExt arch) s)
                                => Ctx.Assignment (LCCR.Atom s) args
                                -> m (LCCR.AtomValue (DMS.MacawExt arch) s ret)
                  -- ^ Syntax extension wrapper that takes the arguments passed
                  -- to the extension operator, returning a suitable crucible
                  -- 'LCCR.AtomValue' to represent it in the syntax extension.
                   }

data SomeExtensionWrapper arch =
  forall args ret. SomeExtensionWrapper (ExtensionWrapper arch args ret)

-- | Helper to create an ExtensionWrapper from just a wrapper function when
-- the argument types have a KnownRepr instance.
mkKnownWrapper
  :: WI.KnownRepr LCT.CtxRepr args
  => (forall s m. ExtensionParser m (DMS.MacawExt arch) s
      => Ctx.Assignment (LCCR.Atom s) args
      -> m (LCCR.AtomValue (DMS.MacawExt arch) s ret))
  -> ExtensionWrapper arch args ret
mkKnownWrapper f = ExtensionWrapper
  { extArgTypes = WI.knownRepr
  , extWrapper = f
  }

-- | Helper to create an ExtensionWrapper from an uncurried function when
-- the argument types have a KnownRepr instance.
mkUncurriedWrapper
  :: forall arch args ret
   . (WI.KnownRepr LCT.CtxRepr args, Ctx.CurryAssignmentClass args)
  => (forall s m. ExtensionParser m (DMS.MacawExt arch) s
      => Ctx.CurryAssignment args (LCCR.Atom s) (m (LCCR.AtomValue (DMS.MacawExt arch) s ret)))
  -> ExtensionWrapper arch args ret
mkUncurriedWrapper f = ExtensionWrapper
  { extArgTypes = WI.knownRepr
  , extWrapper = wrapper
  }
  where
    wrapper :: forall s m. ExtensionParser m (DMS.MacawExt arch) s
            => Ctx.Assignment (LCCR.Atom s) args
            -> m (LCCR.AtomValue (DMS.MacawExt arch) s ret)
    wrapper args = Ctx.uncurryAssignment (f @s @m) args

-- | Check that a 'WI.NatRepr' containing a value in bits is a multiple of 8.
-- If so, pass the result of the value divided by 8 (i.e., as bytes) to the
-- continuation. Otherwise, return a default result.
bitsToBytes ::
  WI.NatRepr bits ->
  a ->
  -- ^ Default value to use if @bits@ is not a multiple of 8
  (forall bytes. ((8 WI.* bytes) ~ bits) => WI.NatRepr bytes -> a) ->
  -- ^ Continuation to invoke is @bits@ is a multiple of 8
  a
bitsToBytes bitsRep nonMultipleOf8 multipleOf8 =
  PN.withDivModNat bitsRep w8 $ \bytesRep modRep ->
    case PN.isZeroNat modRep of
      PN.NonZeroNat -> nonMultipleOf8
      PN.ZeroNat
        |  PN.Refl <- PN.mulComm bytesRep w8
        -> multipleOf8 bytesRep
  where
    w8 = PN.knownNat @8

-- | Perform a case analysis on the type argument to @pointer-read@ or
-- @pointer-write@. If the supplied type is not supported, return 'empty'.
-- This function packages factors out all of the grungy pattern-matching and
-- constraint wrangling that @pointer-read@ and @pointer-write@ share in
-- common.
withSupportedPointerReadWriteTypes ::
  Alternative f =>
  LCT.TypeRepr tp ->
  -- ^ The type argument
  (forall bits bytes.
     ( tp ~ LCT.BVType bits
     , (8 WI.* bytes) ~ bits
     , 1 <= bits
     , 1 <= bytes
     ) =>
     WI.NatRepr bits ->
     WI.NatRepr bytes ->
     f a) ->
  -- ^ Continuation to use if the argument is @'LCT.BVRepr (8 'WI.*' bytes)@
  -- (for some positive number @bytes@).
  (forall bits bytes.
     ( tp ~ LCLM.LLVMPointerType bits
     , (8 WI.* bytes) ~ bits
     , 1 <= bits
     , 1 <= bytes
     ) =>
     WI.NatRepr bits ->
     WI.NatRepr bytes ->
     f a) ->
  -- ^ Continuation to use if the argument is
  -- @'LCLM.LLVMPointerRepr (8 'WI.*' bytes)@ (for some positive number
  -- @bytes@).
  f a
withSupportedPointerReadWriteTypes tp bvK ptrK =
  case tp of
    LCT.BVRepr bits ->
      bitsToBytes bits empty $ \bytes ->
        case PN.isPosNat bytes of
          Nothing -> empty
          Just PN.LeqProof -> bvK bits bytes
    LCLM.LLVMPointerRepr bits ->
      bitsToBytes bits empty $ \bytes ->
        case PN.isPosNat bytes of
          Nothing -> empty
          Just PN.LeqProof -> ptrK bits bytes
    _ -> empty

-- | Parser for syntax extensions to crucible syntax
--
-- Note that the return value is a 'Pair.Pair', which seems a bit strange
-- because the 'LCT.TypeRepr' in the first of the pair is redundant (it can be
-- recovered by inspecting the 'LCCR.Atom'). The return value is set up this way
-- because the use site of the parser in crucible-syntax expects the 'Pair.Pair'
-- for all of the parsers that it attempts; returning the 'Pair.Pair' here
-- simplifies the use site.
extensionParser :: forall s m ext arch w
                 . ( ExtensionParser m ext s
                   , ext ~ (DMS.MacawExt arch)
                   , w ~ DMC.ArchAddrWidth arch
                   , KnownNat w
                   , DMM.MemWidth w
                   )
                => Map.Map LCSA.AtomName (SomeExtensionWrapper arch)
                -- ^ Mapping from names to syntax extensions
                -> LCSC.ParserHooks ext
                -- ^ ParserHooks for the desired syntax extension
                -> m (Some (LCCR.Atom s))
                -- ^ A pair containing a result type and an atom of that type
extensionParser wrappers hooks =
  let ?parserHooks = hooks in
  LCSM.depCons LCSC.atomName $ \name ->
    case name of
      LCSA.AtomName "pointer-read" -> do
        -- Pointer reads are a special case because we must parse the type of
        -- the value to read as well as the endianness of the read before
        -- parsing the additional arguments as Atoms.
        LCSM.depCons LCSC.isType $ \(Some tp) -> do
          LCSM.depCons endianness $ \end ->
            let readWrapper = buildPointerReadWrapper tp end in
            go (SomeExtensionWrapper readWrapper)
      LCSA.AtomName "pointer-write" -> do
        -- Pointer writes are a special case because we must parse the type of
        -- the value to write out as well as the endianness of the write before
        -- parsing the additional arguments as Atoms.
        LCSM.depCons LCSC.isType $ \(Some tp) ->
          LCSM.depCons endianness $ \end ->
            let writeWrapper = buildPointerWriteWrapper tp end in
            go (SomeExtensionWrapper writeWrapper)
      LCSA.AtomName "pointer-cond-read" -> do
        LCSM.depCons LCSC.isType $ \(Some tp) -> do
          LCSM.depCons endianness $ \end ->
            let readWrapper = buildPointerCondReadWrapper tp end in
            go (SomeExtensionWrapper readWrapper)
      LCSA.AtomName "pointer-cond-write" -> do
        LCSM.depCons LCSC.isType $ \(Some tp) ->
          LCSM.depCons endianness $ \end ->
            let writeWrapper = buildPointerCondWriteWrapper tp end in
            go (SomeExtensionWrapper writeWrapper)
      LCSA.AtomName "bv-typed-literal" -> do
        -- Bitvector literals with a type argument are a special case.  We must
        -- parse the type argument separately before parsing the remaining
        -- argument as an Atom.
        LCSM.depCons LCSC.isType $ \(Some tp) ->
          case tp of
            LCT.BVRepr{} ->
              go (SomeExtensionWrapper (buildBvTypedLitWrapper tp))
            _ -> empty
      LCSA.AtomName "overflows" -> do
        LCSM.depCons overflowOp $ \op ->
          LCSM.depCons LCSC.isType $ \(Some tp) ->
            case tp of
              LCT.BVRepr bvWidth ->
                WI.withKnownNat bvWidth $
                  go (SomeExtensionWrapper (wrapMacawOverflows op bvWidth))
              _ -> empty
      LCSA.AtomName "fresh-symbolic" -> do
        LCSM.depCons parseMacawType $ \(Some macawTp) ->
          go (SomeExtensionWrapper (buildMacawFreshSymbolicWrapper macawTp))
      LCSA.AtomName "global-ptr" -> do
        LCSM.depCons LCSC.nat $ \region ->
          LCSM.depCons LCSC.nat $ \offset ->
            go (SomeExtensionWrapper (buildMacawGlobalPtrWrapper (fromIntegral region) offset))
      LCSA.AtomName "pointer-trunc" -> do
        LCSM.depCons LCSC.isType $ \(Some srcTp) ->
          LCSM.depCons LCSC.isType $ \(Some tgtTp) ->
            case (srcTp, tgtTp) of
              (LCT.BVRepr srcWidth, LCT.BVRepr tgtWidth) ->
                case PN.testLeq (PN.addNat tgtWidth (PN.knownNat @1)) srcWidth of
                  Just PN.LeqProof ->
                    WI.withKnownNat srcWidth $
                      WI.withKnownNat tgtWidth $
                        go (SomeExtensionWrapper (buildPointerTruncWrapper srcWidth tgtWidth))
                  Nothing -> empty
              _ -> empty
      LCSA.AtomName "pointer-uext" -> do
        LCSM.depCons LCSC.isType $ \(Some srcTp) ->
          LCSM.depCons LCSC.isType $ \(Some tgtTp) ->
            case (srcTp, tgtTp) of
              (LCT.BVRepr srcWidth, LCT.BVRepr tgtWidth) ->
                case PN.testLeq (PN.addNat srcWidth (PN.knownNat @1)) tgtWidth of
                  Just PN.LeqProof ->
                    WI.withKnownNat srcWidth $
                      WI.withKnownNat tgtWidth $
                        go (SomeExtensionWrapper (buildPointerUExtWrapper srcWidth tgtWidth))
                  Nothing -> empty
              _ -> empty
      _ ->
        case Map.lookup name wrappers of
          Nothing -> empty
          Just w -> go w
  where
    go :: (?parserHooks :: LCSC.ParserHooks ext)
       => SomeExtensionWrapper arch
       -> m (Some (LCCR.Atom s))
    go (SomeExtensionWrapper wrapper) = do
      loc <- LCSM.position
      -- Generate atoms for the arguments to this extension
      operandAtoms <- LCSC.operands (extArgTypes wrapper)
      -- Pass these atoms to the extension wrapper and return an atom for the
      -- resulting value
      atomVal <- extWrapper wrapper operandAtoms
      endAtom <- LCSC.freshAtom loc atomVal
      return (Some endAtom)

    -- Parse an 'LCSA.AtomName' representing an endianness into a
    -- 'DMM.Endianness'
    endianness = do
      LCSA.AtomName nm <- LCSC.atomName
      case nm of
        "le" -> pure DMM.LittleEndian
        "be" -> pure DMM.BigEndian
        _ -> empty

    overflowOp = do
      LCSA.AtomName nm <- LCSC.atomName
      case nm of
        "uadc" -> pure DMS.Uadc
        "sadc" -> pure DMS.Sadc
        "usbb" -> pure DMS.Usbb
        "ssbb" -> pure DMS.Ssbb
        _ -> empty

-- | Wrap a statement extension binary operator
binop :: (KnownNat w, Monad m)
      => (  WI.NatRepr w
         -> lhsType
         -> rhsType
         -> LCCE.StmtExtension ext (LCCR.Atom s) tp )
      -- ^ Binary operator
      -> lhsType
      -- ^ Left-hand side operand
      -> rhsType
      -- ^ Right-hand side operand
      -> m (LCCR.AtomValue ext s tp)
binop op lhs rhs =
  return (LCCR.EvalExt (op WI.knownNat lhs rhs))


-- | Wrap a syntax extension binary operator, converting a bitvector in the
-- right-hand side position to an 'LLVMPointerType' before wrapping.
binopRhsBvToPtr :: ( ext ~ DMS.MacawExt arch
                   , ExtensionParser m ext s
                   , 1 <= w
                   , KnownNat w )
                => (  WI.NatRepr w
                   -> lhsType
                   -> LCCR.Atom s (LCLM.LLVMPointerType w)
                   -> LCCE.StmtExtension ext (LCCR.Atom s) tp)
                -- ^ Binary operator taking an 'LLVMPointerType' in the
                -- right-hand side position
                -> lhsType
                -- ^ Left-hand side operand
                -> LCCR.Atom s (LCT.BVType w)
                -- ^ Right-hand side operand as a bitvector to convert to an
                -- 'LLVMPointerType'
                -> m (LCCR.AtomValue ext s tp)
binopRhsBvToPtr op p1 p2 = do
  toPtrAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr WI.knownNat p2)))
  binop op p1 toPtrAtom

-- | Wrapper for the 'DMS.PtrAdd' syntax extension that enables users to add
-- integer offsets to pointers:
--
-- > pointer-add ptr offset
--
-- Note that the underlying macaw primitive allows the offset to be in either
-- position. This user-facing interface is more restrictive.
wrapPointerAdd
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCT.BVType w)
                      (LCLM.LLVMPointerType w)
wrapPointerAdd = mkUncurriedWrapper $ binopRhsBvToPtr DMS.PtrAdd

-- | Wrapper for the 'DMS.PtrSub' syntax extension that enables users to
-- subtract integer offsets from pointers:
--
-- > pointer-sub ptr offset
--
-- Note that the underlying macaw primitive allows the offset to be in either
-- position. This user-facing interface is more restrictive.
wrapPointerSub
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCT.BVType w)
                      (LCLM.LLVMPointerType w)
wrapPointerSub = mkUncurriedWrapper $ binopRhsBvToPtr (DMS.PtrSub . DMM.addrWidthRepr)

-- | Compute the difference between two pointers in bytes using 'DMS.PtrSub'
pointerDiff :: ( w ~ DMC.ArchAddrWidth arch
               , ext ~ DMS.MacawExt arch
               , ExtensionParser m ext s
               , KnownNat w
               , DMM.MemWidth w )
            => LCCR.Atom s (LCLM.LLVMPointerType w)
            -> LCCR.Atom s (LCLM.LLVMPointerType w)
            -> m (LCCR.AtomValue ext s (LCT.BVType w))
pointerDiff lhs rhs = do
  ptrRes <- binop (DMS.PtrSub . DMM.addrWidthRepr) lhs rhs
  ptrAtom <- LCSC.freshAtom WP.InternalPos ptrRes
  -- 'DMS.PtrSub' of two pointers produces a bitvector (LLVMPointer with region
  -- 0) so 'DMS.PtrToBits' is safe here.
  return (LCCR.EvalApp (LCE.ExtensionApp (DMS.PtrToBits LCT.knownNat ptrAtom)))

-- | Wrapper for the 'DMS.PtrSub' syntax extension that enables users to
-- subtract pointers from pointers:
--
-- > pointer-diff ptr1 ptr2
wrapPointerDiff
  :: ( w ~ DMC.ArchAddrWidth arch
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w )
                      (LCT.BVType w)
wrapPointerDiff = mkUncurriedWrapper pointerDiff

wrapPointerBinop
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => (forall s.
      DMM.AddrWidthRepr (DMC.ArchAddrWidth arch)
      -> LCCR.Atom s (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
      -> LCCR.Atom s (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
      -> DMS.MacawStmtExtension arch (LCCR.Atom s) (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch)))
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w)
                      (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
wrapPointerBinop op = mkUncurriedWrapper $ binop (op . DMM.addrWidthRepr)

wrapPointerAnd
  :: ( w ~ DMC.ArchAddrWidth arch
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w )
                      (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
wrapPointerAnd =
  wrapPointerBinop DMS.PtrAnd

wrapPointerXor
  :: ( w ~ DMC.ArchAddrWidth arch
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w )
                      (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
wrapPointerXor =
  wrapPointerBinop DMS.PtrXor

wrapPointerMux
  :: ( w ~ DMC.ArchAddrWidth arch
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCT.BoolType
                                    Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w )
                      (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
wrapPointerMux = mkUncurriedWrapper $ \b l r ->
  pure $ LCCR.EvalExt $ DMS.PtrMux (DMM.addrWidthRepr WI.knownNat) b l r

-- | Wrapper for 'DMS.MacawNullPtr' to construct a null pointer.
--
-- > pointer-make-null
wrapMakeNull
  :: ( w ~ DMC.ArchAddrWidth arch
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      Ctx.EmptyCtx
                      (LCLM.LLVMPointerType w)
wrapMakeNull = mkKnownWrapper $ \_ ->
  let nullptr = DMS.MacawNullPtr (DMC.addrWidthRepr WI.knownNat)
  in return (LCCR.EvalApp (LCE.ExtensionApp nullptr))

-- | Wrapper for the 'DMS.BitsToPtr' syntax extension that enables users to
-- convert a bitvector to a pointer.
--
-- > bits-to-pointer bv
wrapBitsToPointer
  :: ( w ~ DMC.ArchAddrWidth arch
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCT.BVType w)
                      (LCLM.LLVMPointerType w)
wrapBitsToPointer = mkUncurriedWrapper $ \bv ->
  pure $ LCCR.EvalApp $ LCE.ExtensionApp $ DMS.BitsToPtr WI.knownNat bv

-- | Wrapper for the 'DMS.PtrToBits' syntax extension that enables users to
-- convert a pointer to a bitvector by extracting the pointer offset.
--
-- > pointer-to-bits bv
wrapPointerToBits
  :: ( w ~ DMC.ArchAddrWidth arch
     , KnownNat w
     , DMC.MemWidth w )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                      (LCT.BVType w)
wrapPointerToBits = mkUncurriedWrapper $ \ptr ->
  pure $ LCCR.EvalApp $ LCE.ExtensionApp $ DMS.PtrToBits WI.knownNat ptr

wrapPointerCmp
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => (forall s.
      DMM.AddrWidthRepr (DMC.ArchAddrWidth arch)
      -> LCCR.Atom s (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
      -> LCCR.Atom s (LCLM.LLVMPointerType (DMC.ArchAddrWidth arch))
      -> DMS.MacawStmtExtension arch (LCCR.Atom s) LCT.BoolType)
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w)
                      LCT.BoolType
wrapPointerCmp op = mkUncurriedWrapper $ binop (op . DMM.addrWidthRepr)

-- | Wrapper for the 'DMS.PtrEq' syntax extension that enables users to test
-- the equality of two pointers.
--
-- > pointer-eq ptr1 ptr2
wrapPointerEq
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w)
                      LCT.BoolType
wrapPointerEq = wrapPointerCmp DMS.PtrEq

-- | Wrapper for the 'DMS.PtrLeq' syntax extension that enables users to compare
-- two pointers.
--
-- > pointer-leq ptr1 ptr2
wrapPointerLeq
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w)
                      LCT.BoolType
wrapPointerLeq =  wrapPointerCmp DMS.PtrLeq

-- | Wrapper for the 'DMS.PtrLt' syntax extension that enables users to compare
-- two pointers.
--
-- > pointer-lt ptr1 ptr2
wrapPointerLt
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch )
  => ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> LCLM.LLVMPointerType w)
                      LCT.BoolType
wrapPointerLt =  wrapPointerCmp DMS.PtrLt

-- | Wrapper for the 'DMS.MacawReadMem' syntax extension that enables users to
-- read through a pointer to retrieve data at the underlying memory location.
--
-- > pointer-read type endianness ptr
buildPointerReadWrapper
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     )
  => LCT.TypeRepr tp
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                      tp
buildPointerReadWrapper tp endianness = mkUncurriedWrapper $
  pointerRead tp endianness

-- | Read through a pointer using 'DMS.MacawReadMem'.
pointerRead :: ( w ~ DMC.ArchAddrWidth arch
               , DMM.MemWidth w
               , KnownNat w
               , ExtensionParser m ext s
               , ext ~ DMS.MacawExt arch
               )
            => LCT.TypeRepr tp
            -> DMM.Endianness
            -> LCCR.Atom s (LCLM.LLVMPointerType w)
            -> m (LCCR.AtomValue ext s tp)
pointerRead tp endianness ptr =
  withSupportedPointerReadWriteTypes tp
    (\bits bytes -> do -- `Bitvector w` case
      let readInfo = DMC.BVMemRepr bytes endianness
      let readExt = DMS.MacawReadMem (DMC.addrWidthRepr WI.knownNat) readInfo ptr
      readAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalExt readExt)
      return (LCCR.EvalApp (LCE.ExtensionApp (DMS.PtrToBits bits readAtom))))
    (\_bits bytes -> do -- `Pointer` case
      let readInfo = DMC.BVMemRepr bytes endianness
      let readExt = DMS.MacawReadMem (DMC.addrWidthRepr WI.knownNat) readInfo ptr
      return (LCCR.EvalExt readExt))

-- | Wrapper for the 'DMS.MacawWriteMem' syntax extension that enables users to
-- write data through a pointer to the underlying memory location.
--
-- > pointer-write type endianness ptr (val :: type)
buildPointerWriteWrapper
  :: ( w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , KnownNat w
     , ext ~ DMS.MacawExt arch
     )
  => LCT.TypeRepr tp
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> tp)
                      LCT.UnitType
buildPointerWriteWrapper tp endianness = ExtensionWrapper
  { extArgTypes = Ctx.empty Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> tp
  , extWrapper = Ctx.uncurryAssignment (pointerWrite tp endianness)
  }

-- | Read through a pointer using 'DMS.MacawWriteMem'.
pointerWrite :: ( w ~ DMC.ArchAddrWidth arch
                , DMM.MemWidth w
                , KnownNat w
                , ExtensionParser m ext s
                , ext ~ DMS.MacawExt arch
                )
              => LCT.TypeRepr tp
              -> DMM.Endianness
              -> LCCR.Atom s (LCLM.LLVMPointerType w)
              -> LCCR.Atom s tp
              -> m (LCCR.AtomValue ext s LCT.UnitType)
pointerWrite tp endianness ptr val =
  withSupportedPointerReadWriteTypes tp
    (\bits bytes -> do -- `Bitvector w` case
      toPtrAtom <- LCSC.freshAtom WP.InternalPos
        (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr bits val)))
      let writeInfo = DMC.BVMemRepr bytes endianness
      let writeExt = DMS.MacawWriteMem (DMC.addrWidthRepr WI.knownNat)
                                       writeInfo
                                       ptr
                                       toPtrAtom
      return (LCCR.EvalExt writeExt))
    (\_bits bytes -> do -- `Pointer` case
      let writeInfo = DMC.BVMemRepr bytes endianness
      let writeExt = DMS.MacawWriteMem (DMC.addrWidthRepr WI.knownNat)
                                       writeInfo
                                       ptr
                                       val
      return (LCCR.EvalExt writeExt))

-- | Wrapper for the 'DMS.MacawCondReadMem' syntax extension that enables users to
-- conditionally read through a pointer.
--
-- > pointer-cond-read type endianness condition ptr default-value
buildPointerCondReadWrapper
  :: ( KnownNat w
     , DMC.MemWidth w
     , w ~ DMC.ArchAddrWidth arch
     )
  => LCT.TypeRepr tp
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCT.BoolType
                                    Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> tp)
                      tp
buildPointerCondReadWrapper tp endianness = ExtensionWrapper
  { extArgTypes = Ctx.empty Ctx.:> LCT.BoolRepr
                            Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> tp
  , extWrapper = Ctx.uncurryAssignment (pointerCondRead tp endianness)
  }

-- | Conditionally read through a pointer using 'DMS.MacawCondReadMem'.
pointerCondRead :: ( w ~ DMC.ArchAddrWidth arch
                   , DMM.MemWidth w
                   , KnownNat w
                   , ExtensionParser m ext s
                   , ext ~ DMS.MacawExt arch
                   )
                => LCT.TypeRepr tp
                -> DMM.Endianness
                -> LCCR.Atom s LCT.BoolType
                -> LCCR.Atom s (LCLM.LLVMPointerType w)
                -> LCCR.Atom s tp
                -> m (LCCR.AtomValue ext s tp)
pointerCondRead tp endianness cond ptr defVal =
  withSupportedPointerReadWriteTypes tp
    (\bits bytes -> do -- `Bitvector w` case
      let readInfo = DMC.BVMemRepr bytes endianness
      -- For bitvector case, need to convert the default value to pointer
      defPtrAtom <- LCSC.freshAtom WP.InternalPos
        (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr bits defVal)))
      let readExt = DMS.MacawCondReadMem (DMC.addrWidthRepr WI.knownNat)
                                         readInfo
                                         cond
                                         ptr
                                         defPtrAtom
      readAtom <- LCSC.freshAtom WP.InternalPos (LCCR.EvalExt readExt)
      return (LCCR.EvalApp (LCE.ExtensionApp (DMS.PtrToBits bits readAtom))))
    (\_bits bytes -> do -- `Pointer` case
      let readInfo = DMC.BVMemRepr bytes endianness
      let readExt = DMS.MacawCondReadMem (DMC.addrWidthRepr WI.knownNat)
                                         readInfo
                                         cond
                                         ptr
                                         defVal
      return (LCCR.EvalExt readExt))

-- | Wrapper for the 'DMS.MacawCondWriteMem' syntax extension that enables users to
-- conditionally write data through a pointer.
--
-- > pointer-cond-write type endianness condition ptr value
buildPointerCondWriteWrapper
  :: ( w ~ DMC.ArchAddrWidth arch
     , DMM.MemWidth w
     , KnownNat w
     , ext ~ DMS.MacawExt arch
     )
  => LCT.TypeRepr tp
  -> DMM.Endianness
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCT.BoolType
                                    Ctx.::> LCLM.LLVMPointerType w
                                    Ctx.::> tp)
                      LCT.UnitType
buildPointerCondWriteWrapper tp endianness = ExtensionWrapper
  { extArgTypes = Ctx.empty Ctx.:> LCT.BoolRepr
                            Ctx.:> LCLM.LLVMPointerRepr LCT.knownNat
                            Ctx.:> tp
  , extWrapper = Ctx.uncurryAssignment (pointerCondWrite tp endianness)
  }

-- | Conditionally write through a pointer using 'DMS.MacawCondWriteMem'.
pointerCondWrite :: ( w ~ DMC.ArchAddrWidth arch
                    , DMM.MemWidth w
                    , KnownNat w
                    , ExtensionParser m ext s
                    , ext ~ DMS.MacawExt arch
                    )
                  => LCT.TypeRepr tp
                  -> DMM.Endianness
                  -> LCCR.Atom s LCT.BoolType
                  -> LCCR.Atom s (LCLM.LLVMPointerType w)
                  -> LCCR.Atom s tp
                  -> m (LCCR.AtomValue ext s LCT.UnitType)
pointerCondWrite tp endianness cond ptr val =
  withSupportedPointerReadWriteTypes tp
    (\bits bytes -> do -- `Bitvector w` case
      toPtrAtom <- LCSC.freshAtom WP.InternalPos
        (LCCR.EvalApp (LCE.ExtensionApp (DMS.BitsToPtr bits val)))
      let writeInfo = DMC.BVMemRepr bytes endianness
      let writeExt = DMS.MacawCondWriteMem (DMC.addrWidthRepr WI.knownNat)
                                           writeInfo
                                           cond
                                           ptr
                                           toPtrAtom
      return (LCCR.EvalExt writeExt))
    (\_bits bytes -> do -- `Pointer` case
      let writeInfo = DMC.BVMemRepr bytes endianness
      let writeExt = DMS.MacawCondWriteMem (DMC.addrWidthRepr WI.knownNat)
                                           writeInfo
                                           cond
                                           ptr
                                           val
      return (LCCR.EvalExt writeExt))

-- | Wrapper for constructing bitvector literals matching the size of an
-- 'LCT.BVRepr'.  This enables users to instantiate literals with portable
-- types (such as SizeT).
--
-- > bv-typed-literal type integer
buildBvTypedLitWrapper
  :: LCT.TypeRepr (LCT.BVType w)
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCT.IntegerType)
                      (LCT.BVType w)
buildBvTypedLitWrapper tp = mkUncurriedWrapper $ bvTypedLit tp

-- | Create a bitvector literal matching the size of an 'LCT.BVRepr'
bvTypedLit :: forall s ext w m
           . ( ExtensionParser m ext s )
          => LCT.TypeRepr (LCT.BVType w)
          -> LCCR.Atom s LCT.IntegerType
          -> m (LCCR.AtomValue ext s (LCT.BVType w))
bvTypedLit (LCT.BVRepr w) val = return (LCCR.EvalApp (LCE.IntegerToBV w val))

-- | Wrapper for 'DMS.MacawFreshSymbolic' that generates a fresh symbolic variable.
--
-- > fresh-symbolic type
buildMacawFreshSymbolicWrapper
  :: forall arch tp
   . DMT.TypeRepr tp
  -> ExtensionWrapper arch Ctx.EmptyCtx (DMS.ToCrucibleType tp)
buildMacawFreshSymbolicWrapper tpRepr = mkKnownWrapper $ \_ ->
  return (LCCR.EvalExt (DMS.MacawFreshSymbolic tpRepr))

-- | Parse a Macaw type representation.
--
-- Supports:
-- - MacawBool (simple atom)
-- - (MacawBV 64) (s-expression with width)
parseMacawType :: LCSM.MonadSyntax LCSA.Atomic m
               => m (Some DMT.TypeRepr)
parseMacawType = LCSM.describe "Macaw type" $
  -- Try s-expression first: (MacawBV n)
  (LCSM.depCons LCSC.atomName $ \name ->
      case name of
        LCSA.AtomName "MacawBV" ->
          LCSM.depCons LCSC.nat $ \n ->
            case PN.someNat n of
              Just (Some nRepr) ->
                case PN.isZeroOrGT1 nRepr of
                  Left PN.Refl -> empty  -- width must be >= 1
                  Right PN.LeqProof ->
                    return (Some (DMT.BVTypeRepr nRepr))
              Nothing -> empty
        _ -> empty)
  <|>
  (do name <- LCSC.atomName
      case name of
        LCSA.AtomName "MacawBool" -> return (Some DMT.BoolTypeRepr)
        _ -> empty)

-- | Build a wrapper for 'DMS.PtrTrunc' with explicit source and target widths.
--
-- > pointer-trunc (Bitvector source-width) (Bitvector target-width) ptr
buildPointerTruncWrapper
  :: forall arch w r
   . ( KnownNat w
     , KnownNat r
     , 1 <= r
     , (r + 1) <= w
     , 1 <= w
     )
  => PN.NatRepr w
  -> PN.NatRepr r
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                      (LCLM.LLVMPointerType r)
buildPointerTruncWrapper _wRepr rRepr = mkUncurriedWrapper $
  pure . LCCR.EvalExt . DMS.PtrTrunc rRepr

-- | Build a wrapper for 'DMS.PtrUExt' with explicit source and target widths.
--
-- > pointer-uext (Bitvector source-width) (Bitvector target-width) ptr
buildPointerUExtWrapper
  :: forall arch w r
   . ( KnownNat w
     , KnownNat r
     , 1 <= w
     , (w + 1) <= r
     , 1 <= r
     )
  => PN.NatRepr w
  -> PN.NatRepr r
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCLM.LLVMPointerType w)
                      (LCLM.LLVMPointerType r)
buildPointerUExtWrapper _wRepr rRepr = mkUncurriedWrapper $
  pure . LCCR.EvalExt . DMS.PtrUExt rRepr

-- | Wrapper for 'DMS.MacawOverflows' expression extension that tests whether
-- an arithmetic operation overflows.
--
-- > overflows op width lhs rhs carry
--
-- Where op is one of: uadc, sadc, usbb, ssbb
wrapMacawOverflows
  :: forall arch w
   . ( KnownNat w
     , 1 <= w
     )
  => DMS.MacawOverflowOp
  -> PN.NatRepr w
  -> ExtensionWrapper arch
                      (Ctx.EmptyCtx Ctx.::> LCT.BVType w
                                    Ctx.::> LCT.BVType w
                                    Ctx.::> LCT.BoolType)
                      LCT.BoolType
wrapMacawOverflows op wRepr = mkUncurriedWrapper $ \lhs rhs carry ->
  pure $ LCCR.EvalApp $ LCE.ExtensionApp $ DMS.MacawOverflows op wRepr lhs rhs carry

-- | Wrapper for 'DMS.MacawGlobalPtr' that converts a memory address to a pointer.
--
-- > global-ptr region offset
--
-- Takes a region index (integer) and offset (natural) and constructs a MemAddr.
buildMacawGlobalPtrWrapper
  :: forall arch w
   . ( w ~ DMC.ArchAddrWidth arch
     , KnownNat w
     , DMC.MemWidth w
     )
  => Integer
  -> Natural
  -> ExtensionWrapper arch Ctx.EmptyCtx (LCLM.LLVMPointerType w)
buildMacawGlobalPtrWrapper region offset = mkKnownWrapper $ \_ ->
  let addr = DMM.MemAddr
        { DMM.addrBase = fromInteger region
        , DMM.addrOffset = fromIntegral offset
        }
  in return (LCCR.EvalExt (DMS.MacawGlobalPtr (DMM.addrWidthRepr (Proxy :: Proxy w)) addr))

-- | Syntax extension wrappers
extensionWrappers
  :: (w ~ DMC.ArchAddrWidth arch, KnownNat w, DMC.MemWidth w)
  => Map.Map LCSA.AtomName (SomeExtensionWrapper arch)
extensionWrappers = Map.fromList
  [ (LCSA.AtomName "pointer-add", SomeExtensionWrapper wrapPointerAdd)
  , (LCSA.AtomName "pointer-diff", SomeExtensionWrapper wrapPointerDiff)
  , (LCSA.AtomName "pointer-sub", SomeExtensionWrapper wrapPointerSub)
  , (LCSA.AtomName "pointer-and", SomeExtensionWrapper wrapPointerAnd)
  , (LCSA.AtomName "pointer-xor", SomeExtensionWrapper wrapPointerXor)
  , (LCSA.AtomName "pointer-mux", SomeExtensionWrapper wrapPointerMux)
  , (LCSA.AtomName "pointer-eq", SomeExtensionWrapper wrapPointerEq)
  , (LCSA.AtomName "pointer-leq", SomeExtensionWrapper wrapPointerLeq)
  , (LCSA.AtomName "pointer-lt", SomeExtensionWrapper wrapPointerLt)
  , (LCSA.AtomName "pointer-make-null", SomeExtensionWrapper wrapMakeNull)
  , (LCSA.AtomName "pointer-to-bits", SomeExtensionWrapper wrapPointerToBits)
  , (LCSA.AtomName "bits-to-pointer", SomeExtensionWrapper wrapBitsToPointer)
  ]

ptrTypeParser :: LCSM.MonadSyntax LCSA.Atomic m => m (Some LCT.TypeRepr)
ptrTypeParser = LCSM.describe "Pointer type" $ do
  LCSC.BoundedNat n <- LCLS.pointerTypeParser
  pure (Some (LCLM.LLVMPointerRepr n))

-- | All of the crucible syntax extensions to support machine code
machineCodeParserHooks
  :: forall w arch proxy
   . (w ~ DMC.ArchAddrWidth arch, KnownNat w, DMC.MemWidth w)
  => proxy arch
  -- | Hooks with which to further extend this parser
  -> LCSC.ParserHooks (DMS.MacawExt arch)
  -> LCSC.ParserHooks (DMS.MacawExt arch)
machineCodeParserHooks proxy hooks =
  LCSC.ParserHooks
  { LCSC.extensionTypeParser =
      LCSM.describe "Macaw type" $
        LCSM.call (ptrTypeParser <|> LCSC.extensionTypeParser hooks)
  , LCSC.extensionParser =
      LCSM.describe "Macaw operation" $ do
        let extParser = extensionParser extensionWrappers (machineCodeParserHooks proxy hooks)
        LCSM.call (extParser <|> LCSC.extensionParser hooks)
  }
