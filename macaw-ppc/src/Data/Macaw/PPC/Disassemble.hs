{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.PPC.Disassemble ( disassembleFn ) where

import           Control.Lens ( (&), (^.), (%~), (.~) )
import           Control.Monad ( unless )
import qualified Control.Monad.Except as ET
import           Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )
import           Data.Bits
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Foldable as F
import           Data.Proxy ( Proxy(..) )
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import           Data.Word ( Word64 )
import           Text.Printf ( printf )
import           Debug.Trace

import qualified Dismantle.PPC as D

import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import           Data.Macaw.Types ( BVType, BoolType )
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr ( NatRepr )
import qualified Data.Parameterized.Nonce as NC

import           Data.Macaw.PPC.Generator
import           Data.Macaw.PPC.PPCReg

import Debug.Trace (trace)
import           Text.PrettyPrint.ANSI.Leijen as PP hiding ((<$>))

-- | Read one instruction from the 'MM.Memory' at the given segmented offset.
--
-- Returns the instruction and number of bytes consumed /or/ an error.
--
-- This code assumes that the 'MM.ByteRegion' is maximal; that is, that there
-- are no byte regions that could be coalesced.
readInstruction :: MM.Memory w
                -> MM.MemSegmentOff w
                -> Either (MM.MemoryError w) (D.Instruction, MM.MemWord w)
readInstruction mem addr = MM.addrWidthClass (MM.memAddrWidth mem) $ do
  let seg = MM.msegSegment addr
  case MM.segmentFlags seg `MMP.hasPerm` MMP.execute of
    False -> ET.throwError (MM.PermissionsError (MM.relativeSegmentAddr addr))
    True -> do
      contents <- MM.addrContentsAfter mem (MM.relativeSegmentAddr addr)
      case contents of
        [] -> ET.throwError (MM.AccessViolation (MM.relativeSegmentAddr addr))
        MM.SymbolicRef {} : _ ->
          ET.throwError (MM.UnexpectedRelocation (MM.relativeSegmentAddr addr))
        MM.ByteRegion bs : _rest
          | BS.null bs -> ET.throwError (MM.AccessViolation (MM.relativeSegmentAddr addr))
          | otherwise -> do
            -- FIXME: Having to wrap the bytestring in a lazy wrapper is
            -- unpleasant.  We could alter the disassembler to consume strict
            -- bytestrings, at the cost of possibly making it less efficient for
            -- other clients.
            let (bytesRead, minsn) = D.disassembleInstruction (LBS.fromStrict bs)
            case minsn of
              Just insn -> return (insn, fromIntegral bytesRead)
              Nothing -> ET.throwError (MM.InvalidInstruction (MM.relativeSegmentAddr addr) contents)

{-

Steps for dealing with conditional branches:

 - Extend the value simplifier to handle concat (needed for interpreting branch targets)
 - Detect ~ite~ values assigned to the IP; capture the condition and both targets
 - Cause a split (via ~ContT~) when we find an ~ite~ in the IP

Note that the extension to the value simplifier is needed to interpret
unconditional branch targets as well, as they also have a 2 bit right extension.
It looks like the simplifier will also need to be able to understand OR, shifts,
extensions, and maybe even other operations.

It looks like macaw-x86 has a similar rewriter.  We should write a very general
one and export it as part of the rewriter.  It doesn't need to be in the
rewriter monad.

-}

disassembleBlock :: forall ppc s
                  . PPCArchConstraints ppc
                 => (Value ppc s (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (PPCGenerator ppc s ()))
                 -> MM.Memory (ArchAddrWidth ppc)
                 -> GenState ppc s
                 -> MM.MemSegmentOff (ArchAddrWidth ppc)
                 -> MM.MemWord (ArchAddrWidth ppc)
                 -> DisM ppc s (MM.MemWord (ArchAddrWidth ppc), BlockSeq ppc s)
disassembleBlock lookupSemantics mem gs curIPAddr maxOffset = do
  let seg = MM.msegSegment curIPAddr
  let off = MM.msegOffset curIPAddr
  case readInstruction mem curIPAddr of
    Left err -> failAt gs off curIPAddr (DecodeError err)
    Right (i, bytesRead) -> do
      traceM ("II: " ++ show i)
      let nextIPOffset = off + bytesRead
          nextIP = MM.relativeAddr seg nextIPOffset
          nextIPVal = MC.RelocatableValue (pointerNatRepr (Proxy @ppc)) nextIP
      -- Note: In PowerPC, the IP is incremented *after* an instruction
      -- executes, rather than before as in X86.  We have to pass in the
      -- physical address of the instruction here.
      ipVal <- case MM.asAbsoluteAddr (MM.relativeSegmentAddr curIPAddr) of
                 Nothing -> failAt gs off curIPAddr (InstructionAtUnmappedAddr i)
                 Just addr -> return (BVValue (pointerNatRepr (Proxy @ppc)) (fromIntegral addr))
      case lookupSemantics ipVal i of
        Nothing -> failAt gs off curIPAddr (UnsupportedInstruction i)
        Just transformer -> do
          -- Once we have the semantics for the instruction (represented by a
          -- state transformer), we apply the state transformer and then extract
          -- a result from the state of the 'PPCGenerator'.
          egs1 <- liftST $ runGenerator genResult gs $ do
            let lineStr = printf "%s: %s" (show curIPAddr) (show (D.ppInstruction i))
            addStmt (Comment (T.pack  lineStr))
            transformer
          case egs1 of
            Left genErr -> failAt gs off curIPAddr (GenerationError i genErr)
            Right gs1 -> do
              case resState gs1 of
                Just preBlock
                  | Seq.null (resBlockSeq gs1 ^. frontierBlocks)
                  , v <- preBlock ^. (pBlockState . curIP)
                  , trace ("raw ip = " ++ show (pretty v)) True
                  , Just simplifiedIP <- simplifyValue v
                  , trace ("v = " ++ show (pretty simplifiedIP) ++ "\nnextIPVal = " ++ show nextIPVal ++ "\n") $ simplifiedIP == nextIPVal
                  , nextIPOffset < maxOffset
                  , Just nextIPSegAddr <- MM.asSegmentOff mem nextIP -> do
                      let preBlock' = (pBlockState . curIP .~ simplifiedIP) preBlock
                      let gs2 = GenState { assignIdGen = assignIdGen gs
                                         , _blockSeq = resBlockSeq gs1
                                         , _blockState = preBlock'
                                         , genAddr = nextIPSegAddr
                                         }
                      disassembleBlock lookupSemantics mem gs2 nextIPSegAddr maxOffset


                _ -> return (nextIPOffset, finishBlock FetchAndExecute gs1)

-- | A very restricted value simplifier
--
-- The full rewriter is too heavyweight here, as it produces new bound values
-- instead of fully reducing the calculation we want to a literal.
simplifyValue :: (OrdF (ArchReg arch), MM.MemWidth (ArchAddrWidth arch))
              => Value arch ids tp
              -> Maybe (Value arch ids tp)
simplifyValue v =
  case v of
    BVValue {} -> Just v
    AssignedValue (Assignment { assignRhs = EvalApp app }) ->
      simplifyApp app
    _ -> Nothing

simplifyApp :: forall arch ids tp
             . (OrdF (ArchReg arch), MM.MemWidth (ArchAddrWidth arch))
            => App (Value arch ids) tp
            -> Maybe (Value arch ids tp)
simplifyApp a =
  case a of
    AndApp (BoolValue True) r         -> Just r
    AndApp l (BoolValue True)         -> Just l
    AndApp f@(BoolValue False) _      -> Just f
    AndApp _ f@(BoolValue False)      -> Just f
    OrApp t@(BoolValue True) _        -> Just t
    OrApp _ t@(BoolValue True)        -> Just t
    OrApp (BoolValue False) r         -> Just r
    OrApp l (BoolValue False)         -> Just l
    Mux _ (BoolValue c) t e           -> if c then Just t else Just e
    BVAnd _ l r
      | Just Refl <- testEquality l r -> Just l
    BVAnd sz l r                      -> binopbv (.&.) sz l r
    BVOr  sz l r                      -> binopbv (.|.) sz l r
    BVShl sz l r                      -> binopbv (\l' r' -> shiftL l' (fromIntegral r')) sz l r
    BVAdd _ l (BVValue _ 0)           -> Just l
    BVAdd _ (BVValue _ 0) r           -> Just r
    BVAdd rep l@(BVValue {}) r@(RelocatableValue {}) ->
      simplifyApp (BVAdd rep r l)
    BVAdd rep (RelocatableValue _ addr) (BVValue _ off) ->
      Just (RelocatableValue rep (MM.incAddr off addr))
    BVAdd sz l r                      -> binopbv (+) sz l r
    BVMul _ l (BVValue _ 1)           -> Just l
    BVMul _ (BVValue _ 1) r           -> Just r
    BVMul rep _ (BVValue _ 0)         -> Just (BVValue rep 0)
    BVMul rep (BVValue _ 0) _         -> Just (BVValue rep 0)
    BVMul rep l r                     -> binopbv (*) rep l r
    UExt (BVValue _ n) sz             -> Just (mkLit sz n)
    Trunc (BVValue _ x) sz            -> Just (mkLit sz x)

    Eq l r                            -> boolop (==) l r
    BVComplement sz x                 -> unop complement sz x
    _                                 -> Nothing
  where
    unop :: (tp ~ BVType n)
         => (Integer -> Integer)
         -> NatRepr n
         -> Value arch ids tp
         -> Maybe (Value arch ids tp)
    unop f sz (BVValue _ l) = Just (mkLit sz (f l))
    unop _ _ _ = Nothing

    boolop :: (Integer -> Integer -> Bool)
           -> Value arch ids utp
           -> Value arch ids utp
           -> Maybe (Value arch ids BoolType)
    boolop f (BVValue _ l) (BVValue _ r) = Just (BoolValue (f l r))
    boolop _ _ _ = Nothing

    binopbv :: (tp ~ BVType n)
            => (Integer -> Integer -> Integer)
            -> NatRepr n
            -> Value arch ids tp
            -> Value arch ids tp
            -> Maybe (Value arch ids tp)
    binopbv f sz (BVValue _ l) (BVValue _ r) = Just (mkLit sz (f l r))
    binopbv _ _ _ _ = Nothing

tryDisassembleBlock :: ( PPCArchConstraints ppc
                       , Show (Block ppc s)
                       , Show (BlockSeq ppc s))
                    => (Value ppc s (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (PPCGenerator ppc s ()))
                    -> MM.Memory (ArchAddrWidth ppc)
                    -> NC.NonceGenerator (ST s) s
                    -> ArchSegmentOff ppc
                    -> ArchAddrWord ppc
                    -> DisM ppc s ([Block ppc s], MM.MemWord (ArchAddrWidth ppc))
tryDisassembleBlock lookupSemantics mem nonceGen startAddr maxSize = do
  let gs0 = initGenState nonceGen startAddr (initRegState startAddr)
  let startOffset = MM.msegOffset startAddr
  (nextIPOffset, blocks) <- disassembleBlock lookupSemantics mem gs0 startAddr (startOffset + maxSize)
  traceShow blocks $ unless (nextIPOffset > startOffset) $ do
    let reason = InvalidNextIP (fromIntegral nextIPOffset) (fromIntegral startOffset)
    failAt gs0 nextIPOffset startAddr reason
  return (F.toList (blocks ^. frontierBlocks), nextIPOffset - startOffset)

-- | Disassemble a block from the given start address (which points into the
-- 'MM.Memory').
--
-- Return a list of disassembled blocks as well as the total number of bytes
-- occupied by those blocks.
disassembleFn :: ( PPCArchConstraints ppc
                 , Show (Block ppc s)
                 , Show (BlockSeq ppc s))
              => proxy ppc
              -> (Value ppc s (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (PPCGenerator ppc s ()))
              -- ^ A function to look up the semantics for an instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> MM.Memory (ArchAddrWidth ppc)
              -- ^ The mapped memory space
              -> NC.NonceGenerator (ST s) s
              -- ^ A generator of unique IDs used for assignments
              -> ArchSegmentOff ppc
              -- ^ The address to disassemble from
              -> ArchAddrWord ppc
              -- ^ Maximum size of the block (a safeguard)
              -> MA.AbsBlockState (ArchReg ppc)
              -- ^ Abstract state of the processor at the start of the block
              -> ST s ([Block ppc s], MM.MemWord (ArchAddrWidth ppc), Maybe String)
disassembleFn _ lookupSemantics mem nonceGen startAddr maxSize _  = do
  mr <- ET.runExceptT (unDisM (tryDisassembleBlock lookupSemantics mem nonceGen startAddr maxSize))
  case mr of
    Left (blocks, off, exn) -> return (blocks, off, Just (show exn))
    Right (blocks, bytes) -> traceShow blocks $ return (blocks, bytes, Nothing)

type LocatedError ppc s = ([Block ppc s], MM.MemWord (ArchAddrWidth ppc), TranslationError (ArchAddrWidth ppc))
-- | This is a monad for error handling during disassembly
--
-- It allows for early failure that reports progress (in the form of blocks
-- discovered and the latest address examined) along with a reason for failure
-- (a 'TranslationError').
newtype DisM ppc s a = DisM { unDisM :: ET.ExceptT (LocatedError ppc s) (ST s) a }
  deriving (Functor,
            Applicative,
            Monad)

-- | This funny instance is required because GHC doesn't allow type function
-- applications in instance heads, so we factor the type functions out into a
-- constraint on a fresh variable.  See
--
-- > https://stackoverflow.com/questions/45360959/illegal-type-synonym-family-application-in-instance-with-functional-dependency
--
-- We also can't derive this instance because of that restriction (but deriving
-- silently fails).
instance (w ~ ArchAddrWidth ppc) => ET.MonadError ([Block ppc s], MM.MemWord w, TranslationError w) (DisM ppc s) where
  throwError e = DisM (ET.throwError e)
  catchError a hdlr = do
    r <- liftST $ ET.runExceptT (unDisM a)
    case r of
      Left l -> do
        r' <- liftST $ ET.runExceptT (unDisM (hdlr l))
        case r' of
          Left e -> DisM (ET.throwError e)
          Right res -> return res
      Right res -> return res

data TranslationError w = TranslationError { transErrorAddr :: MM.MemSegmentOff w
                                           , transErrorReason :: TranslationErrorReason w
                                           }

data TranslationErrorReason w = InvalidNextIP Word64 Word64
                              | DecodeError (MM.MemoryError w)
                              | UnsupportedInstruction D.Instruction
                              | InstructionAtUnmappedAddr D.Instruction
                              | GenerationError D.Instruction GeneratorError
                              deriving (Show)

deriving instance (MM.MemWidth w) => Show (TranslationError w)

liftST :: ST s a -> DisM ppc s a
liftST = DisM . lift

-- | Early failure for 'DisM'.  This is a wrapper around 'ET.throwError' that
-- computes the current progress alongside the reason for the failure.
--
-- Note that the 'TranslateError' below is a block terminator marker that notes
-- that translation of the basic block resulted in an error (with the exception
-- string stored as its argument).  This allows macaw to carry errors in the
-- instruction stream, which is useful for debugging and diagnostics.
failAt :: forall ppc s a
        . (ArchReg ppc ~ PPCReg ppc, MM.MemWidth (ArchAddrWidth ppc))
       => GenState ppc s
       -> MM.MemWord (ArchAddrWidth ppc)
       -> MM.MemSegmentOff (ArchAddrWidth ppc)
       -> TranslationErrorReason (ArchAddrWidth ppc)
       -> DisM ppc s a
failAt gs offset curIPAddr reason = do
  let exn = TranslationError { transErrorAddr = curIPAddr
                             , transErrorReason = reason
                             }
  let term = (`TranslateError` T.pack (show exn))
  let b = finishBlock' (gs ^. blockState) term
  let res = _blockSeq gs & frontierBlocks %~ (Seq.|> b)
  let res' = F.toList (res ^. frontierBlocks)
  ET.throwError (res', offset, exn)
