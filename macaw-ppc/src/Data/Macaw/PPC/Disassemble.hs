{-# LANGUAGE DataKinds #-}
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
module Data.Macaw.PPC.Disassemble
  ( disassembleFn
  )
where

import           Control.Lens ( (^.), (.~) )
import           Control.Monad ( unless )
import qualified Control.Monad.Except as ET
import           Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Text as T
import           Data.Word ( Word64 )
import           Text.Printf ( printf )

import qualified Dismantle.PPC as D

import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import           Data.Macaw.Types ( BVType )
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Parameterized.Nonce as NC

import qualified SemMC.Architecture.PPC as SP

import           Data.Macaw.SemMC.Generator
import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Macaw.PPC.Arch ( PPCArchConstraints )

-- | Read one instruction from the 'MM.Memory' at the given segmented offset.
--
-- Returns the instruction and number of bytes consumed /or/ an error.
--
-- This code assumes that the 'MM.ByteRegion' is maximal; that is, that there
-- are no byte regions that could be coalesced.
readInstruction :: (MM.MemWidth w)
                => MM.MemSegmentOff w
                -> Either (PPCMemoryError w) (D.Instruction, MM.MemWord w)
readInstruction addr = do
  let seg = MM.segoffSegment addr
  case MM.segmentFlags seg `MMP.hasPerm` MMP.execute of
    False -> ET.throwError (PPCMemoryError (MM.PermissionsError (MM.segoffAddr addr)))
    True -> do
      contents <- liftMemError $ MM.segoffContentsAfter addr
      case contents of
        [] -> ET.throwError (PPCMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
        MM.RelocationRegion r : _ ->
          ET.throwError (PPCMemoryError (MM.UnexpectedRelocation (MM.segoffAddr addr) r))
        MM.BSSRegion {} : _ ->
          ET.throwError (PPCMemoryError (MM.UnexpectedBSS (MM.segoffAddr addr)))
        MM.ByteRegion bs : _rest
          | BS.null bs -> ET.throwError (PPCMemoryError (MM.AccessViolation (MM.segoffAddr addr)))
          | otherwise -> do
            -- FIXME: Having to wrap the bytestring in a lazy wrapper is
            -- unpleasant.  We could alter the disassembler to consume strict
            -- bytestrings, at the cost of possibly making it less efficient for
            -- other clients.
            let (bytesRead, minsn) = D.disassembleInstruction (LBS.fromStrict bs)
            case minsn of
              Just insn -> return (insn, fromIntegral bytesRead)
              Nothing -> ET.throwError (PPCInvalidInstruction (MM.segoffAddr addr) contents)

liftMemError :: Either (MM.MemoryError w) a -> Either (PPCMemoryError w) a
liftMemError e =
  case e of
    Left err -> Left (PPCMemoryError err)
    Right a -> Right a

-- | A wrapper around the 'MM.MemoryError' that lets us add in information about
-- invalid instructions.
data PPCMemoryError w = PPCInvalidInstruction !(MM.MemAddr w) [MM.MemChunk w]
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
disassembleBlock :: forall var ppc ids s
                  . (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
                 => (Value ppc ids (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (Generator ppc ids s ()))
                 -- ^ A function to look up the semantics for an instruction that we disassemble
                 -> GenState ppc ids s
                 -> MM.MemSegmentOff (ArchAddrWidth ppc)
                 -- ^ The current instruction pointer
                 -> MM.MemWord (ArchAddrWidth ppc)
                 -- ^ The offset into the block of this instruction
                 -> MM.MemWord (ArchAddrWidth ppc)
                 -- ^ The maximum offset into the bytestring that we should
                 -- disassemble to; in principle, macaw can tell us to limit our
                 -- search with this.
                 -> DisM ppc ids s (MM.MemWord (ArchAddrWidth ppc), Block ppc ids)
disassembleBlock lookupSemantics gs curIPAddr blockOff maxOffset = do
  let seg = MM.segoffSegment curIPAddr
  let off = MM.segoffOffset curIPAddr
  case readInstruction curIPAddr of
    Left err -> failAt gs blockOff curIPAddr (DecodeError err)
    Right (i, bytesRead) -> do
--      traceM ("II: " ++ show i)
      let nextIPOffset = off + bytesRead
          nextIP = MM.segmentOffAddr seg nextIPOffset
          nextIPVal = MC.RelocatableValue (MM.addrWidthRepr curIPAddr) nextIP
      -- Note: In PowerPC, the IP is incremented *after* an instruction
      -- executes, rather than before as in X86.  We have to pass in the
      -- physical address of the instruction here.
      let ipVal = MC.BVValue
                    (PN.knownNat @(ArchAddrWidth ppc))
                    (fromIntegral (MM.addrOffset (MM.segoffAddr curIPAddr)))
      case lookupSemantics ipVal i of
        Nothing -> failAt gs blockOff curIPAddr (UnsupportedInstruction i)
        Just transformer -> do
          -- Once we have the semantics for the instruction (represented by a
          -- state transformer), we apply the state transformer and then extract
          -- a result from the state of the 'Generator'.
          egs1 <- liftST $ ET.runExceptT (runGenerator unfinishedBlock gs $ do
            let lineStr = printf "%s: %s" (show curIPAddr) (show (D.ppInstruction i))
            addStmt (InstructionStart blockOff (T.pack lineStr))
            addStmt (Comment (T.pack  lineStr))
            asAtomicStateUpdate (MM.segoffAddr curIPAddr) transformer)
          case egs1 of
            Left genErr -> failAt gs blockOff curIPAddr (GenerationError i genErr)
            Right gs1 -> do
              case gs1 of
                UnfinishedPartialBlock preBlock
                  | v <- preBlock ^. (pBlockState . curIP)
                  , Just simplifiedIP <- simplifyValue v
                  , simplifiedIP == nextIPVal
                  , nextIPOffset < maxOffset
                  , Just nextIPSegAddr <- MM.incSegmentOff curIPAddr (fromIntegral bytesRead) -> do
                      let preBlock' = (pBlockState . curIP .~ simplifiedIP) preBlock
                      let gs2 = GenState { assignIdGen = assignIdGen gs
                                         , _blockState = preBlock'
                                         , genAddr = nextIPSegAddr
                                         , genRegUpdates = MapF.empty
                                         , appCache = appCache gs
                                         , _blockStateSnapshot = preBlock' ^. pBlockState
                                         }
                      disassembleBlock lookupSemantics gs2 nextIPSegAddr (blockOff + 4) maxOffset

                  | otherwise -> return (nextIPOffset, finishBlock' preBlock FetchAndExecute)
                FinishedPartialBlock b -> return (nextIPOffset, b)

tryDisassembleBlock :: (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
                    => (Value ppc ids (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (Generator ppc ids s ()))
                    -> NC.NonceGenerator (ST s) ids
                    -> ArchSegmentOff ppc
                    -> (RegState (ArchReg ppc) (Value ppc ids))
                    -> Int
                    -> DisM ppc ids s (Block ppc ids, Int)
tryDisassembleBlock lookupSemantics nonceGen startAddr regState maxSize = do
  let gs0 = initGenState nonceGen startAddr regState
  let startOffset = MM.segoffOffset startAddr
  (nextIPOffset, block) <- disassembleBlock lookupSemantics gs0 startAddr 0 (startOffset + fromIntegral maxSize)
  unless (nextIPOffset > startOffset) $ do
    let reason = InvalidNextIP (fromIntegral nextIPOffset) (fromIntegral startOffset)
    failAt gs0 0 startAddr reason
  return (block, fromIntegral (nextIPOffset - startOffset))

-- | Disassemble a block from the given start address (which points into the
-- 'MM.Memory').
--
-- Return a list of disassembled blocks as well as the total number of bytes
-- occupied by those blocks.
disassembleFn :: (ppc ~ SP.AnyPPC var, PPCArchConstraints var)
              => proxy var
              -> (Value ppc ids (BVType (ArchAddrWidth ppc)) -> D.Instruction -> Maybe (Generator ppc ids s ()))
              -- ^ A function to look up the semantics for an instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> NC.NonceGenerator (ST s) ids
              -- ^ A generator of unique IDs used for assignments
              -> ArchSegmentOff ppc
              -- ^ The address to disassemble from
              -> (RegState (ArchReg ppc) (Value ppc ids))
              -- ^ The initial registers
              -> Int
              -- ^ Maximum size of the block (a safeguard)
              -> ST s (Block ppc ids, Int)
disassembleFn _ lookupSemantics nonceGen startAddr regState maxSize = do
  mr <- ET.runExceptT (unDisM (tryDisassembleBlock lookupSemantics nonceGen startAddr regState maxSize))
  case mr of
    Left (blocks, bytes, _exn) ->
      -- Note that we discard exn here: it is actually extraneous since the
      -- 'failAt' function converts exceptions raised during translation into
      -- macaw 'TranslationError' block terminators.
      return (blocks, bytes)
    Right (blocks, bytes) -> return (blocks, bytes)

type LocatedError ppc ids = (Block ppc ids, Int, TranslationError (ArchAddrWidth ppc))


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
instance (w ~ ArchAddrWidth ppc) => ET.MonadError (Block ppc ids, Int, TranslationError w) (DisM ppc ids s) where
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
failAt :: forall v ids s a
        . (MM.MemWidth (SP.AddrWidth v))
       => GenState (SP.AnyPPC v) ids s
       -> MM.MemWord (SP.AddrWidth v)
       -> MM.MemSegmentOff (SP.AddrWidth v)
       -> TranslationErrorReason (SP.AddrWidth v)
       -> DisM (SP.AnyPPC v) ids s a
failAt gs bytesConsumed curIPAddr reason = do
  let exn = TranslationError { transErrorAddr = curIPAddr
                             , transErrorReason = reason
                             }
  let term = (`TranslateError` T.pack (show exn))
  let b = finishBlock' (gs ^. blockState) term
  ET.throwError (b, fromIntegral bytesConsumed, exn)
