{-# LANGUAGE DeriveFunctor #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.ARM.Disassemble
    ( disassembleFn
    )
    where

import           Control.Lens ( (&), (^.), (%~), (.~) )
import           Control.Monad ( unless )
import qualified Control.Monad.Except as ET
import           Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )
import qualified Data.ByteString as BS
import qualified Data.ByteString.Lazy as LBS
import qualified Data.Foldable as F
import           Data.Macaw.ARM.ARMReg
import           Data.Macaw.ARM.Arch ( ARMArchConstraints )
import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as MMP
import           Data.Macaw.SemMC.Generator
import           Data.Macaw.SemMC.Simplify ( simplifyValue )
import           Data.Macaw.Types -- ( BVType, BoolType )
import           Data.Maybe ( fromMaybe )
import qualified Data.Parameterized.Nonce as NC
import           Data.Proxy ( Proxy(..) )
import qualified Data.Sequence as Seq
import qualified Data.Text as T
import           Data.Word ( Word32 )
import qualified Dismantle.ARM as ARMD
import           Text.Printf ( printf )


-- | Disassemble a block from the given start address (which points into the
-- 'MM.Memory').
--
-- Return a list of disassembled blocks as well as the total number of bytes
-- occupied by those blocks.
disassembleFn :: (ARMArchConstraints arm)
              => proxy arm
              -> (Value arm ids (BVType (ArchAddrWidth arm)) -> ARMD.Instruction -> Maybe (Generator arm ids s ()))
              -- ^ A function to look up the semantics for an instruction.  The
              -- lookup is provided with the value of the IP in case IP-relative
              -- addressing is necessary.
              -> MM.Memory (ArchAddrWidth arm)
              -- ^ The mapped memory space
              -> NC.NonceGenerator (ST s) ids
              -- ^ A generator of unique IDs used for assignments
              -> ArchSegmentOff arm
              -- ^ The address to disassemble from
              -> ArchAddrWord arm
              -- ^ Maximum size of the block (a safeguard)
              -> MA.AbsBlockState (ArchReg arm)
              -- ^ Abstract state of the processor at the start of the block
              -> ST s ([Block arm ids], MM.MemWord (ArchAddrWidth arm), Maybe String)
disassembleFn _ lookupSemantics mem nonceGen startAddr maxSize _  = do
  mr <- ET.runExceptT (unDisM (tryDisassembleBlock
                              lookupSemantics mem nonceGen startAddr maxSize))
  case mr of
    Left (blocks, off, exn) -> return (blocks, off, Just (show exn))
    Right (blocks, bytes) -> return (blocks, bytes, Nothing)

tryDisassembleBlock :: (ARMArchConstraints arm)
                    => (Value arm ids (BVType (ArchAddrWidth arm)) -> ARMD.Instruction -> Maybe (Generator arm ids s ()))
                    -> MM.Memory (ArchAddrWidth arm)
                    -> NC.NonceGenerator (ST s) ids
                    -> ArchSegmentOff arm
                    -> ArchAddrWord arm
                    -> DisM arm ids s ([Block arm ids], MM.MemWord (ArchAddrWidth arm))
tryDisassembleBlock lookupSemantics mem nonceGen startAddr maxSize = do
  let gs0 = initGenState nonceGen mem startAddr (initRegState startAddr)
  let startOffset = MM.msegOffset startAddr
  (nextPCOffset, blocks) <- disassembleBlock lookupSemantics mem gs0 startAddr (startOffset + maxSize)
  unless (nextPCOffset > startOffset) $ do
    let reason = InvalidNextPC (fromIntegral nextPCOffset) (fromIntegral startOffset)
    failAt gs0 nextPCOffset startAddr reason
  return (F.toList (blocks ^. frontierBlocks), nextPCOffset - startOffset)



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
disassembleBlock :: forall arm ids s
                  . ARMArchConstraints arm
                 => (Value arm ids (BVType (ArchAddrWidth arm)) -> ARMD.Instruction -> Maybe (Generator arm ids s ()))
                 -- ^ A function to look up the semantics for an instruction that we disassemble
                 -> MM.Memory (ArchAddrWidth arm)
                 -> GenState arm ids s
                 -> MM.MemSegmentOff (ArchAddrWidth arm)
                 -- ^ The current instruction pointer
                 -> MM.MemWord (ArchAddrWidth arm)
                 -- ^ The maximum offset into the bytestring that we should
                 -- disassemble to; in principle, macaw can tell us to limit our
                 -- search with this.
                 -> DisM arm ids s (MM.MemWord (ArchAddrWidth arm), BlockSeq arm ids)
disassembleBlock lookupSemantics mem gs curPCAddr maxOffset = do
  let seg = MM.msegSegment curPCAddr
  let off = MM.msegOffset curPCAddr
  case readInstruction mem curPCAddr of
    Left err -> failAt gs off curPCAddr (DecodeError err)
    Right (i, bytesRead) -> do
      -- traceM ("II: " ++ show i)
      let nextPCOffset = off + bytesRead
          nextPC = MM.relativeAddr seg nextPCOffset
          nextPCVal = MC.RelocatableValue (knownNat :: NatRepr (ArchAddrWidth arm)) nextPC
      -- Note: In ARM, the IP is incremented *after* an instruction
      -- executes; pass in the physical address of the instruction here.
      ipVal <- case MM.asAbsoluteAddr (MM.relativeSegmentAddr curPCAddr) of
                 Nothing -> failAt gs off curPCAddr (InstructionAtUnmappedAddr i)
                 Just addr -> return (BVValue (knownNat :: NatRepr (ArchAddrWidth arm)) (fromIntegral addr))
      case lookupSemantics ipVal i of
        Nothing -> failAt gs off curPCAddr (UnsupportedInstruction i)
        Just transformer -> do
          -- Once we have the semantics for the instruction (represented by a
          -- state transformer), we apply the state transformer and then extract
          -- a result from the state of the 'Generator'.
          egs1 <- liftST $ ET.runExceptT (runGenerator genResult gs $ do
            let lineStr = printf "%s: %s" (show curPCAddr) (show (ARMD.ppInstruction i))
            addStmt (Comment (T.pack  lineStr))
            transformer

            -- Check to see if the PC has become conditionally-defined (by e.g.,
            -- a mux).  If it has, we need to split execution using a primitive
            -- provided by the Generator monad.
            nextPCExpr <- getRegValue ARM_PC
            case matchConditionalBranch nextPCExpr of
              Just (cond, t_pc, f_pc) ->
                conditionalBranch cond (setRegVal ARM_PC t_pc) (setRegVal ARM_PC f_pc)
              Nothing -> return ())
          case egs1 of
            Left genErr -> failAt gs off curPCAddr (GenerationError i genErr)
            Right gs1 -> do
              case resState gs1 of
                Just preBlock
                  | Seq.null (resBlockSeq gs1 ^. frontierBlocks)
                  , v <- preBlock ^. (pBlockState . curIP)
                  , Just simplifiedIP <- simplifyValue v
                  , simplifiedIP == nextPCVal
                  , nextPCOffset < maxOffset
                  , Just nextPCSegAddr <- MM.asSegmentOff mem nextPC -> do
                      let preBlock' = (pBlockState . curIP .~ simplifiedIP) preBlock
                      let gs2 = GenState { assignIdGen = assignIdGen gs
                                         , _blockSeq = resBlockSeq gs1
                                         , _blockState = preBlock'
                                         , genAddr = nextPCSegAddr
                                         , genMemory = mem
                                         }
                      disassembleBlock lookupSemantics mem gs2 nextPCSegAddr maxOffset

                _ -> return (nextPCOffset, finishBlock FetchAndExecute gs1)

-- | Read one instruction from the 'MM.Memory' at the given segmented offset.
--
-- Returns the instruction and number of bytes consumed /or/ an error.
--
-- This code assumes that the 'MM.ByteRegion' is maximal; that is, that there
-- are no byte regions that could be coalesced.
readInstruction :: MM.Memory w
                -> MM.MemSegmentOff w
                -> Either (MM.MemoryError w) (ARMD.Instruction, MM.MemWord w)
readInstruction mem addr = MM.addrWidthClass (MM.memAddrWidth mem) $ do
  let seg = MM.msegSegment addr
      segRelAddr = MM.relativeSegmentAddr addr
  if MM.segmentFlags seg `MMP.hasPerm` MMP.execute
  then do
      contents <- MM.addrContentsAfter mem segRelAddr
      case contents of
        [] -> ET.throwError $ MM.AccessViolation segRelAddr
        MM.SymbolicRef {} : _ ->
          ET.throwError $ MM.UnexpectedRelocation segRelAddr
        MM.ByteRegion bs : _
          | BS.null bs -> ET.throwError $ MM.AccessViolation segRelAddr
          | otherwise -> do
            -- FIXME: Having to wrap the bytestring in a lazy wrapper is
            -- unpleasant.  We could alter the disassembler to consume strict
            -- bytestrings, at the cost of possibly making it less efficient for
            -- other clients.
            let (bytesRead, minsn) = ARMD.disassembleInstruction (LBS.fromStrict bs)
            case minsn of
              Just insn -> return (insn, fromIntegral bytesRead)
              Nothing -> ET.throwError $ MM.InvalidInstruction segRelAddr contents
  else ET.throwError $ MM.PermissionsError segRelAddr

-- | Examine a value and see if it is a mux; if it is, break the mux up and
-- return its component values (the condition and two alternatives)
matchConditionalBranch :: (ARMArchConstraints arch)
                       => Value arch ids tp
                       -> Maybe (Value arch ids BoolType
                               , Value arch ids tp
                               , Value arch ids tp)
matchConditionalBranch v =
  case v of
    AssignedValue (Assignment { assignRhs = EvalApp a }) ->
      case a of
        Mux _rep cond t f -> Just (cond, fromMaybe t (simplifyValue t), fromMaybe f (simplifyValue f))
        _ -> Nothing
    _ -> Nothing


type LocatedError ppc ids = ([Block ppc ids]
                            , MM.MemWord (ArchAddrWidth ppc)
                            , TranslationError (ArchAddrWidth ppc))

-- | This is a monad for error handling during disassembly
--
-- It allows for early failure that reports progress (in the form of blocks
-- discovered and the latest address examined) along with a reason for failure
-- (a 'TranslationError').
newtype DisM ppc ids s a = DisM { unDisM :: ET.ExceptT (LocatedError ppc ids) (ST s) a }
    deriving (Functor, Applicative, Monad)

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

data TranslationErrorReason w = InvalidNextPC Word32 Word32
                              | DecodeError (MM.MemoryError w)
                              | UnsupportedInstruction ARMD.Instruction
                              | InstructionAtUnmappedAddr ARMD.Instruction
                              | GenerationError ARMD.Instruction GeneratorError
                              deriving (Show)

deriving instance (MM.MemWidth w) => Show (TranslationError w)

liftST :: ST s a -> DisM arm ids s a
liftST = DisM . lift


-- | Early failure for 'DisM'.  This is a wrapper around 'ET.throwError' that
-- computes the current progress alongside the reason for the failure.
--
-- Note that the 'TranslateError' below is a block terminator marker that notes
-- that translation of the basic block resulted in an error (with the exception
-- string stored as its argument).  This allows macaw to carry errors in the
-- instruction stream, which is useful for debugging and diagnostics.
failAt :: forall arm ids s a
        . (ArchReg arm ~ ARMReg, MM.MemWidth (ArchAddrWidth arm))
       => GenState arm ids s
       -> MM.MemWord (ArchAddrWidth arm)
       -> MM.MemSegmentOff (ArchAddrWidth arm)
       -> TranslationErrorReason (ArchAddrWidth arm)
       -> DisM arm ids s a
failAt gs offset curPCAddr reason = do
  let exn = TranslationError { transErrorAddr = curPCAddr
                             , transErrorReason = reason
                             }
  let term = (`TranslateError` T.pack (show exn))
  let b = finishBlock' (gs ^. blockState) term
  let res = _blockSeq gs & frontierBlocks %~ (Seq.|> b)
  let res' = F.toList (res ^. frontierBlocks)
  ET.throwError (res', offset, exn)
