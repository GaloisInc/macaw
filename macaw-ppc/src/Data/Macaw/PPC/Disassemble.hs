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
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Foldable as F
import           Data.Maybe ( fromMaybe )
import           Data.Proxy ( Proxy(..) )
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import           Data.Word ( Word64 )
import           Text.Printf ( printf )

import qualified Dismantle.PPC as D

import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import           Data.Macaw.Types ( BVType, BoolType )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as NC

import           Data.Macaw.SemMC.Generator
import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Macaw.PPC.Arch ( PPCArchConstraints )
import           Data.Macaw.PPC.PPCReg

-- | Read one instruction from the 'MM.Memory' at the given segmented offset.
--
-- Returns the instruction and number of bytes consumed /or/ an error.
--
-- This code assumes that the 'MM.ByteRegion' is maximal; that is, that there
-- are no byte regions that could be coalesced.
readInstruction :: MM.Memory w
                -> MM.MemSegmentOff w
                -> Either (PPCMemoryError w) (D.Instruction, MM.MemWord w)
readInstruction mem addr = MM.addrWidthClass (MM.memAddrWidth mem) $ do
  let seg = MM.msegSegment addr
  case MM.segmentFlags seg `MMP.hasPerm` MMP.execute of
    False -> ET.throwError (PPCMemoryError (MM.PermissionsError (MM.relativeSegmentAddr addr)))
    True -> do
      contents <- liftMemError $ MM.addrContentsAfter mem (MM.relativeSegmentAddr addr)
      case contents of
        [] -> ET.throwError (PPCMemoryError (MM.AccessViolation (MM.relativeSegmentAddr addr)))
        MM.RelocationRegion r : _ ->
          ET.throwError (PPCMemoryError (MM.UnexpectedRelocation (MM.relativeSegmentAddr addr) r))
        MM.BSSRegion {} : _ ->
          ET.throwError (PPCMemoryError (MM.UnexpectedBSS (MM.relativeSegmentAddr addr)))
        MM.ByteRegion bs : _rest
          | BS.null bs -> ET.throwError (PPCMemoryError (MM.AccessViolation (MM.relativeSegmentAddr addr)))
          | otherwise -> do
            -- FIXME: Having to wrap the bytestring in a lazy wrapper is
            -- unpleasant.  We could alter the disassembler to consume strict
            -- bytestrings, at the cost of possibly making it less efficient for
            -- other clients.
            let (bytesRead, minsn) = D.disassembleInstruction (LBS.fromStrict bs)
            case minsn of
              Just insn -> return (insn, fromIntegral bytesRead)
              Nothing -> ET.throwError (PPCInvalidInstruction (MM.relativeSegmentAddr addr) contents)

liftMemError :: Either (MM.MemoryError w) a -> Either (PPCMemoryError w) a
liftMemError e =
  case e of
    Left err -> Left (PPCMemoryError err)
    Right a -> Right a

-- | A wrapper around the 'MM.MemoryError' that lets us add in information about
-- invalid instructions.
data PPCMemoryError w = PPCInvalidInstruction !(MM.MemAddr w) [MM.SegmentRange w]
                      | PPCMemoryError !(MM.MemoryError w)
                      deriving (Show)

-- | Disassemble an instruction and terminate the current block if we run out of
-- instructions to disassemble.  We can run out if:
--
-- 1) We exceed the offset that macaw has told us to disassemble to
--
-- 2) We can't decode the IP (i.e., it isn't a constant)
--
-- 3) The IP after executing the semantics transformer is not equal to the
--    expected next IP value, which indicates a jump to another block or
--    function
--
-- In most of those cases, we end the block with a simple terminator.  If the IP
-- becomes a mux, we split execution using 'conditionalBranch'.
disassembleBlock :: forall ppc ids s
                  . PPCArchConstraints ppc
                 => (Value ppc ids (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (Generator ppc ids s ()))
                 -- ^ A function to look up the semantics for an instruction that we disassemble
                 -> MM.Memory (ArchAddrWidth ppc)
                 -> GenState ppc ids s
                 -> MM.MemSegmentOff (ArchAddrWidth ppc)
                 -- ^ The current instruction pointer
                 -> MM.MemWord (ArchAddrWidth ppc)
                 -- ^ The maximum offset into the bytestring that we should
                 -- disassemble to; in principle, macaw can tell us to limit our
                 -- search with this.
                 -> DisM ppc ids s (MM.MemWord (ArchAddrWidth ppc), BlockSeq ppc ids)
disassembleBlock lookupSemantics mem gs curIPAddr maxOffset = do
  let seg = MM.msegSegment curIPAddr
  let off = MM.msegOffset curIPAddr
  case readInstruction mem curIPAddr of
    Left err -> failAt gs off curIPAddr (DecodeError err)
    Right (i, bytesRead) -> do
--      traceM ("II: " ++ show i)
      let nextIPOffset = off + bytesRead
          nextIP = MM.relativeAddr seg nextIPOffset
          nextIPVal = MC.RelocatableValue (MM.addrWidthRepr curIPAddr) nextIP
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
          -- a result from the state of the 'Generator'.
          egs1 <- liftST $ ET.runExceptT (runGenerator genResult gs $ do
            let lineStr = printf "%s: %s" (show curIPAddr) (show (D.ppInstruction i))
            addStmt (Comment (T.pack  lineStr))
            asAtomicStateUpdate (MM.relativeSegmentAddr curIPAddr) transformer

            -- Check to see if the IP has become conditionally-defined (by e.g.,
            -- a mux).  If it has, we need to split execution using a primitive
            -- provided by the Generator monad.
            nextIPExpr <- getRegValue PPC_IP
            case matchConditionalBranch nextIPExpr of
              Just (cond, t_ip, f_ip) ->
                conditionalBranch cond (setRegVal PPC_IP t_ip) (setRegVal PPC_IP f_ip)
              Nothing -> return ())
          case egs1 of
            Left genErr -> failAt gs off curIPAddr (GenerationError i genErr)
            Right gs1 -> do
              case resState gs1 of
                Just preBlock
                  | Seq.null (resBlockSeq gs1 ^. frontierBlocks)
                  , v <- preBlock ^. (pBlockState . curIP)
                  , Just simplifiedIP <- simplifyValue v
                  , simplifiedIP == nextIPVal
                  , nextIPOffset < maxOffset
                  , Just nextIPSegAddr <- MM.asSegmentOff mem nextIP -> do
                      let preBlock' = (pBlockState . curIP .~ simplifiedIP) preBlock
                      let gs2 = GenState { assignIdGen = assignIdGen gs
                                         , _blockSeq = resBlockSeq gs1
                                         , _blockState = preBlock'
                                         , genAddr = nextIPSegAddr
                                         , genMemory = mem
                                         , genRegUpdates = MapF.empty
                                         }
                      disassembleBlock lookupSemantics mem gs2 nextIPSegAddr maxOffset

                _ -> return (nextIPOffset, finishBlock FetchAndExecute gs1)

-- | Examine a value and see if it is a mux; if it is, break the mux up and
-- return its component values (the condition and two alternatives)
matchConditionalBranch :: (PPCArchConstraints arch)
                       => Value arch ids tp
                       -> Maybe (Value arch ids BoolType, Value arch ids tp, Value arch ids tp)
matchConditionalBranch v =
  case v of
    AssignedValue (Assignment { assignRhs = EvalApp a }) ->
      case a of
        Mux _rep cond t f -> Just (cond, fromMaybe t (simplifyValue t), fromMaybe f (simplifyValue f))
        _ -> Nothing
    _ -> Nothing

tryDisassembleBlock :: (PPCArchConstraints ppc)
                    => (Value ppc ids (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (Generator ppc ids s ()))
                    -> MM.Memory (ArchAddrWidth ppc)
                    -> NC.NonceGenerator (ST s) ids
                    -> ArchSegmentOff ppc
                    -> ArchAddrWord ppc
                    -> DisM ppc ids s ([Block ppc ids], MM.MemWord (ArchAddrWidth ppc))
tryDisassembleBlock lookupSemantics mem nonceGen startAddr maxSize = do
  let gs0 = initGenState nonceGen mem startAddr (initRegState startAddr)
  let startOffset = MM.msegOffset startAddr
  (nextIPOffset, blocks) <- disassembleBlock lookupSemantics mem gs0 startAddr (startOffset + maxSize)
  unless (nextIPOffset > startOffset) $ do
    let reason = InvalidNextIP (fromIntegral nextIPOffset) (fromIntegral startOffset)
    failAt gs0 nextIPOffset startAddr reason
  return (F.toList (blocks ^. frontierBlocks), nextIPOffset - startOffset)

-- | Disassemble a block from the given start address (which points into the
-- 'MM.Memory').
--
-- Return a list of disassembled blocks as well as the total number of bytes
-- occupied by those blocks.
disassembleFn :: (PPCArchConstraints ppc)
              => proxy ppc
              -> (Value ppc ids (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (Generator ppc ids s ()))
              -- ^ A function to look up the semantics for an instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> MM.Memory (ArchAddrWidth ppc)
              -- ^ The mapped memory space
              -> NC.NonceGenerator (ST s) ids
              -- ^ A generator of unique IDs used for assignments
              -> ArchSegmentOff ppc
              -- ^ The address to disassemble from
              -> ArchAddrWord ppc
              -- ^ Maximum size of the block (a safeguard)
              -> MA.AbsBlockState (ArchReg ppc)
              -- ^ Abstract state of the processor at the start of the block
              -> ST s ([Block ppc ids], MM.MemWord (ArchAddrWidth ppc), Maybe String)
disassembleFn _ lookupSemantics mem nonceGen startAddr maxSize _  = do
  mr <- ET.runExceptT (unDisM (tryDisassembleBlock lookupSemantics mem nonceGen startAddr maxSize))
  case mr of
    Left (blocks, off, exn) -> return (blocks, off, Just (show exn))
    Right (blocks, bytes) -> return (blocks, bytes, Nothing)

type LocatedError ppc ids = ([Block ppc ids], MM.MemWord (ArchAddrWidth ppc), TranslationError (ArchAddrWidth ppc))
-- | This is a monad for error handling during disassembly
--
-- It allows for early failure that reports progress (in the form of blocks
-- discovered and the latest address examined) along with a reason for failure
-- (a 'TranslationError').
newtype DisM ppc ids s a = DisM { unDisM :: ET.ExceptT (LocatedError ppc ids) (ST s) a }
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
instance (w ~ ArchAddrWidth ppc) => ET.MonadError ([Block ppc ids], MM.MemWord w, TranslationError w) (DisM ppc ids s) where
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
                              | DecodeError (PPCMemoryError w)
                              | UnsupportedInstruction D.Instruction
                              | InstructionAtUnmappedAddr D.Instruction
                              | GenerationError D.Instruction GeneratorError
                              deriving (Show)

deriving instance (MM.MemWidth w) => Show (TranslationError w)

liftST :: ST s a -> DisM ppc ids s a
liftST = DisM . lift

-- | Early failure for 'DisM'.  This is a wrapper around 'ET.throwError' that
-- computes the current progress alongside the reason for the failure.
--
-- Note that the 'TranslateError' below is a block terminator marker that notes
-- that translation of the basic block resulted in an error (with the exception
-- string stored as its argument).  This allows macaw to carry errors in the
-- instruction stream, which is useful for debugging and diagnostics.
failAt :: forall ppc ids s a
        . (ArchReg ppc ~ PPCReg ppc, MM.MemWidth (ArchAddrWidth ppc))
       => GenState ppc ids s
       -> MM.MemWord (ArchAddrWidth ppc)
       -> MM.MemSegmentOff (ArchAddrWidth ppc)
       -> TranslationErrorReason (ArchAddrWidth ppc)
       -> DisM ppc ids s a
failAt gs offset curIPAddr reason = do
  let exn = TranslationError { transErrorAddr = curIPAddr
                             , transErrorReason = reason
                             }
  let term = (`TranslateError` T.pack (show exn))
  let b = finishBlock' (gs ^. blockState) term
  let res = _blockSeq gs & frontierBlocks %~ (Seq.|> b)
  let res' = F.toList (res ^. frontierBlocks)
  ET.throwError (res', offset, exn)
