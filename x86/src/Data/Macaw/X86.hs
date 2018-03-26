{-
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>

This defines the primitives needed to provide architecture info for
x86_64 programs.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.X86
       ( x86_64_freeBSD_info
       , x86_64_linux_info
       , freeBSD_syscallPersonality
       , linux_syscallPersonality
         -- * Low level exports
       , ExploreLoc
       , rootLoc
       , disassembleBlock
       , X86TranslateError(..)
       , Data.Macaw.X86.ArchTypes.X86_64
       , Data.Macaw.X86.ArchTypes.X86PrimFn(..)
       , Data.Macaw.X86.ArchTypes.X86Stmt(..)
       , Data.Macaw.X86.ArchTypes.X86TermStmt(..)
       , Data.Macaw.X86.X86Reg.X86Reg(..)
       , Data.Macaw.X86.X86Reg.x86ArgumentRegs
       , Data.Macaw.X86.X86Reg.x86ResultRegs
       , Data.Macaw.X86.X86Reg.x86FloatArgumentRegs
       , Data.Macaw.X86.X86Reg.x86FloatResultRegs
       , Data.Macaw.X86.X86Reg.x86CalleeSavedRegs
       , pattern Data.Macaw.X86.X86Reg.RAX
       , x86DemandContext
       ) where

import           Control.Exception (assert)
import           Control.Lens
import           Control.Monad.Cont
import           Control.Monad.Except
import           Control.Monad.ST
import qualified Data.Foldable as Fold
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Flexdis86 as F
import           Text.PrettyPrint.ANSI.Leijen (Pretty(..), text)

import           Data.Macaw.AbsDomain.AbsState
       ( AbsBlockState
       , setAbsIP
       , absRegState
       , StackEntry(..)
       , concreteStackOffset
       , AbsValue(..)
       , top
       , stridedInterval
       , asConcreteSingleton
       , startAbsStack
       , hasMaximum
       , AbsProcessorState
       , transferValue
       , CallParams(..)
       , absEvalCall
       )
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types
  ( n8
  , n64
  , HasRepr(..)
  )
import           Data.Macaw.X86.ArchTypes
import           Data.Macaw.X86.Flexdis
import           Data.Macaw.X86.Semantics (execInstruction)
import           Data.Macaw.X86.SyscallInfo
import           Data.Macaw.X86.SyscallInfo.FreeBSD as FreeBSD
import           Data.Macaw.X86.SyscallInfo.Linux as Linux
import           Data.Macaw.X86.X86Reg

import           Data.Macaw.X86.Generator

------------------------------------------------------------------------
-- ExploreLoc

-- | This represents the control-flow information needed to build basic blocks
-- for a code location.
data ExploreLoc
   = ExploreLoc { loc_ip      :: !(MemSegmentOff 64)
                  -- ^ IP address.
                , loc_x87_top :: !Int
                  -- ^ Top register of x87 stack
                , loc_df_flag :: !Bool
                  -- ^ Value of DF flag
                }
 deriving (Eq, Ord)

instance Pretty ExploreLoc where
  pretty loc = text $ show (loc_ip loc)

rootLoc :: MemSegmentOff 64 -> ExploreLoc
rootLoc ip = ExploreLoc { loc_ip      = ip
                        , loc_x87_top = 7
                        , loc_df_flag = False
                        }

initX86State :: ExploreLoc -- ^ Location to explore from.
             -> RegState X86Reg (Value X86_64 ids)
initX86State loc = mkRegState Initial
                 & curIP     .~ RelocatableValue knownNat (relativeSegmentAddr (loc_ip loc))
                 & boundValue X87_TopReg .~ mkLit knownNat (toInteger (loc_x87_top loc))
                 & boundValue DF         .~ BoolValue (loc_df_flag loc)

------------------------------------------------------------------------
-- Location


initGenState :: NonceGenerator (ST st_s) ids
             -> Memory 64
             -> MemSegmentOff 64
                -- ^ Address of initial instruction
             -> RegState X86Reg (Value X86_64 ids)
                -- ^ Initial register state
             -> GenState st_s ids
initGenState nonce_gen mem addr s =
    GenState { assignIdGen = nonce_gen
             , _blockSeq = BlockSeq { _nextBlockID    = 1
                                    , _frontierBlocks = Seq.empty
                                    }
             , _blockState     = emptyPreBlock s 0 addr
             , genAddr = addr
             , genMemory = mem
             , avxMode = False
             }

-- | Describes the reason the translation error occured.
data X86TranslateErrorReason
   = DecodeError (MemoryError 64)
     -- ^ A memory error occured in decoding with Flexdis
   | UnsupportedInstruction F.InstructionInstance
     -- ^ The instruction is not supported by the translator
   | ExecInstructionError F.InstructionInstance Text
     -- ^ An error occured when trying to translate the instruction

-- | Describes an error that occured in translation
data X86TranslateError = X86TranslateError { transErrorAddr :: !(MemSegmentOff 64)
                                           , transErrorReason :: !X86TranslateErrorReason
                                           }

instance Show X86TranslateError where
  show err =
      case transErrorReason err of
        DecodeError me ->
          "Memory error at " ++ addr ++ ": " ++ show me
        UnsupportedInstruction i ->
          "Unsupported instruction at " ++ addr ++ ": " ++ show i
        ExecInstructionError i msg ->
          "Error in interpretting instruction at " ++ addr ++ ": " ++ show i ++ "\n  "
          ++ Text.unpack msg
    where addr = show (transErrorAddr err)

returnWithError :: GenState st_s ids
                -> X86TranslateErrorReason
                -> ST st_s (BlockSeq ids, MemWord 64, Maybe X86TranslateError)
returnWithError gs rsn =
  let curIPAddr = genAddr gs
      err = X86TranslateError curIPAddr rsn
      term = (`TranslateError` Text.pack (show err))
      b = finishBlock' (gs^.blockState) term
      res = seq b $ gs^.blockSeq & frontierBlocks %~ (Seq.|> b)
   in return (res, msegOffset curIPAddr, Just err)

-- | Translate block, returning blocks read, ending
-- PC, and an optional error.  and ending PC.
disassembleBlockImpl :: forall st_s ids
                     .  GenState st_s ids
                     -- ^ State information for translation
                     -> MemWord 64
                         -- ^ Maximum offset for this addr.
                     -> [SegmentRange 64]
                        -- ^ List of contents to read next.
                     -> ST st_s (BlockSeq ids, MemWord 64, Maybe X86TranslateError)
disassembleBlockImpl gs max_offset contents = do
  let curIPAddr = genAddr gs
  case readInstruction' curIPAddr contents of
    Left msg -> do
      returnWithError gs (DecodeError msg)
    Right (i, next_ip_off) -> do
      let seg = msegSegment curIPAddr
      let off = msegOffset curIPAddr
      let next_ip :: MemAddr 64
          next_ip = relativeAddr seg next_ip_off
      let next_ip_val :: BVValue X86_64 ids 64
          next_ip_val = RelocatableValue n64 next_ip
      case execInstruction (ValueExpr next_ip_val) i of
        Nothing -> do
          returnWithError gs (UnsupportedInstruction i)
        Just exec -> do
          gsr <-
            runExceptT $ runX86Generator (\() s -> pure (mkGenResult s)) gs $ do
              let next_ip_word = fromIntegral $ segmentOffset seg + off
              let line = show curIPAddr ++ ": " ++ show (F.ppInstruction next_ip_word i)
              addStmt (Comment (Text.pack line))
              exec
          case gsr of
            Left msg -> do
              returnWithError gs (ExecInstructionError i msg)
            Right res -> do
              case resState res of
                -- If IP after interpretation is the next_ip, there are no blocks, and we
                -- haven't crossed max_offset, then keep running.
                Just p_b
                  | Seq.null (resBlockSeq res ^. frontierBlocks)
                  , RelocatableValue _ v <- p_b^.(pBlockState . curIP)
                  , v == next_ip
                    -- Check to see if we should continue
                  , next_ip_off < max_offset
                  , Just next_ip_segaddr <- resolveSegmentOff seg next_ip_off -> do
                 let gs2 = GenState { assignIdGen = assignIdGen gs
                                    , _blockSeq = resBlockSeq res
                                    , _blockState = p_b
                                    , genAddr = next_ip_segaddr
                                    , genMemory = genMemory gs
                                    , avxMode = avxMode gs
                                    }
                 case dropSegmentRangeListBytes contents (fromIntegral (next_ip_off - off)) of
                   Left msg -> do
                     let err = dropErrorAsMemError (relativeSegmentAddr curIPAddr) msg
                     returnWithError gs (DecodeError err)
                   Right contents' ->
                     disassembleBlockImpl gs2 max_offset contents'
                _ -> do
                  let gs3 = finishBlock FetchAndExecute res
                  return (gs3, next_ip_off, Nothing)

-- | Disassemble block, returning either an error, or a list of blocks
-- and ending PC.
disassembleBlock :: forall s
                 .  Memory 64
                 -> NonceGenerator (ST s) s
                 -> ExploreLoc
                 -> MemWord 64
                    -- ^ Maximum number of bytes in ths block.
                 -> ST s ([Block X86_64 s], MemWord 64, Maybe X86TranslateError)
disassembleBlock mem nonce_gen loc max_size = do
  let addr = loc_ip loc
  let gs = initGenState nonce_gen mem addr (initX86State loc)
  let sz = msegOffset addr + max_size
  (gs', next_ip_off, maybeError) <-
    case addrContentsAfter mem (relativeSegmentAddr addr) of
      Left msg ->
        returnWithError gs (DecodeError msg)
      Right contents ->
        disassembleBlockImpl gs sz contents
  assert (next_ip_off > msegOffset addr) $ do
  let block_sz = next_ip_off - msegOffset addr
  pure (Fold.toList (gs'^.frontierBlocks), block_sz, maybeError)

-- | The abstract state for a function begining at a given address.
initialX86AbsState :: MemSegmentOff 64 -> AbsBlockState X86Reg
initialX86AbsState addr
  = top
  & setAbsIP addr
  & absRegState . boundValue sp_reg .~ concreteStackOffset (relativeSegmentAddr addr) 0
  -- x87 top register points to top of stack.
  & absRegState . boundValue X87_TopReg .~ FinSet (Set.singleton 7)
  -- Direction flag is initially zero.
  & absRegState . boundValue DF .~ BoolConst False
  & startAbsStack .~ Map.singleton 0 (StackEntry (BVMemRepr n8 LittleEndian) ReturnAddr)

preserveFreeBSDSyscallReg :: X86Reg tp -> Bool
preserveFreeBSDSyscallReg r
  | Just Refl <- testEquality r CF  = False
  | Just Refl <- testEquality r RAX = False
  | otherwise = True

-- | Linux preserves the same registers the x86_64 ABI does
linuxSystemCallPreservedRegisters :: Set.Set (Some X86Reg)
linuxSystemCallPreservedRegisters = x86CalleeSavedRegs


-- | Transfer some type into an abstract value given a processor state.
transferAbsValue :: AbsProcessorState X86Reg ids
                 -> X86PrimFn (Value X86_64 ids) tp
                 -> AbsValue 64 tp
transferAbsValue r f =
  case f of
    EvenParity _ -> TopV
    ReadLoc _  -> TopV
    ReadFSBase -> TopV
    ReadGSBase -> TopV
    CPUID _    -> TopV
    RDTSC      -> TopV
    XGetBV _   -> TopV
    PShufb{}   -> TopV
      -- We know only that it will return up to (and including(?)) cnt
    MemCmp _sz cnt _src _dest _rev
      | Just upper <- hasMaximum knownRepr (transferValue r cnt) ->
          stridedInterval $ SI.mkStridedInterval knownNat False 0 upper 1
      | otherwise -> TopV
    RepnzScas _sz _val _buf cnt
      | Just upper <- hasMaximum knownRepr (transferValue r cnt) ->
          stridedInterval $ SI.mkStridedInterval knownNat False 0 upper 1
      | otherwise -> TopV
    MMXExtend{}   -> TopV
    X86IDiv{} -> TopV
    X86IRem{} -> TopV
    X86Div{}  -> TopV
    X86Rem{}  -> TopV
    SSE_VectorOp{}  -> TopV
    SSE_CMPSX{}  -> TopV
    SSE_UCOMIS{}  -> TopV
    SSE_CVTSD2SS{}  -> TopV
    SSE_CVTSS2SD{}  -> TopV
    SSE_CVTSI2SX{}  -> TopV
    SSE_CVTTSX2SI{}  -> TopV
    X87_Extend{}  -> TopV
    X87_FST{}  -> TopV
    X87_FAdd{}  -> TopV
    X87_FSub{}  -> TopV
    X87_FMul{}  -> TopV

    -- XXX: Is 'TopV' the right thing for the AVX instruction below?
    VOp1 {} -> TopV
    VOp2 {} -> TopV
    Pointwise2 {} -> TopV
    PointwiseShiftL {} -> TopV
    VExtractF128 {} -> TopV
    VInsert {} -> TopV

-- | Disassemble block, returning either an error, or a list of blocks
-- and ending PC.
tryDisassembleBlockFromAbsState :: forall s ids
                                .  Memory 64
                                -> NonceGenerator (ST s) ids
                                -> MemSegmentOff 64
                                -- ^ Address to disassemble at
                                -> MemWord 64
                                -- ^ Maximum size of this block
                                -> AbsBlockState X86Reg
                                -- ^ Abstract state of processor for defining state.
                                -> ExceptT String (ST s) ([Block X86_64 ids], MemWord 64, Maybe String)
tryDisassembleBlockFromAbsState mem nonce_gen addr max_size ab = do
  t <-
    case asConcreteSingleton (ab^.absRegState^.boundValue X87_TopReg) of
      Nothing -> throwError "Could not determine height of X87 stack."
      Just t -> pure t
  d <-
    case asConcreteSingleton (ab^.absRegState^.boundValue DF) of
      Nothing -> do
        throwError $ "Could not determine df flag " ++ show (ab^.absRegState^.boundValue DF)
      Just d -> pure d
  let loc = ExploreLoc { loc_ip = addr
                       , loc_x87_top = fromInteger t
                       , loc_df_flag = d /= 0
                       }
  let gs = initGenState nonce_gen mem addr (initX86State loc)
  let off = msegOffset  addr
  (gs', next_ip_off, maybeError) <- lift $
    case addrContentsAfter mem (relativeSegmentAddr addr) of
      Left msg ->
        returnWithError gs (DecodeError msg)
      Right contents -> do
        disassembleBlockImpl gs (off + max_size) contents
  assert (next_ip_off > off) $ do
  let sz = next_ip_off - off
  let blocks = Fold.toList (gs'^.frontierBlocks)
  pure $! (blocks, sz, show <$> maybeError)

-- | Disassemble block, returning either an error, or a list of blocks
-- and ending PC.
disassembleBlockFromAbsState :: forall s ids
                             .  Memory 64
                             -> NonceGenerator (ST s) ids
                             -> MemSegmentOff 64
                             -- ^ Address to disassemble at
                             -> MemWord 64
                             -- ^ Maximum size of this block
                             -> AbsBlockState X86Reg
                             -- ^ Abstract state of processor for defining state.
                             -> ST s ([Block X86_64 ids], MemWord 64, Maybe String)
disassembleBlockFromAbsState mem nonce_gen addr max_size ab = do
  mr <- runExceptT $ tryDisassembleBlockFromAbsState mem nonce_gen addr max_size ab
  case mr of
    Left msg -> pure ([], 0, Just msg)
    Right r ->  pure r

-- | Attempt to identify the write to a stack return address, returning
-- instructions prior to that write and return  values.
--
-- This can also return Nothing if the call is not supported.
identifyX86Call :: Memory 64
                -> [Stmt X86_64 ids]
                -> RegState X86Reg (Value X86_64 ids)
                -> Maybe (Seq (Stmt X86_64 ids), MemSegmentOff 64)
identifyX86Call mem stmts0 s = go (Seq.fromList stmts0) Seq.empty
  where -- Get value of stack pointer
        next_sp = s^.boundValue sp_reg
        -- Recurse on statements.
        go stmts after =
          case Seq.viewr stmts of
            Seq.EmptyR -> Nothing
            prev Seq.:> stmt
              -- Check for a call statement by determining if the last statement
              -- writes an executable address to the stack pointer.
              | WriteMem a _repr val <- stmt
              , Just _ <- testEquality a next_sp
                -- Check this is the right length.
              , Just Refl <- testEquality (typeRepr next_sp) (typeRepr val)
                -- Check if value is a valid literal address
              , Just val_a <- valueAsMemAddr val
                -- Check if segment of address is marked as executable.
              , Just ret_addr <- asSegmentOff mem val_a
              , segmentFlags (msegSegment ret_addr) `Perm.hasPerm` Perm.execute ->
                Just (prev Seq.>< after, ret_addr)
                -- Stop if we hit any architecture specific instructions prior to
                -- identifying return address since they may have side effects.
              | ExecArchStmt _ <- stmt -> Nothing
                -- Otherwise skip over this instruction.
              | otherwise -> go prev (stmt Seq.<| after)

-- | This is designed to detect returns from the register state representation.
--
-- It pattern matches on a 'RegState' to detect if it read its instruction
-- pointer from an address that stored on the stack pointer.
identifyX86Return :: [Stmt X86_64 ids]
                  -> RegState X86Reg (Value X86_64 ids)
                  -> Maybe [Stmt X86_64 ids]
identifyX86Return stmts s = do
  -- How stack pointer moves when a call is made
  let stack_adj = -8
  let next_ip = s^.boundValue ip_reg
      next_sp = s^.boundValue sp_reg
  case next_ip of
    AssignedValue (Assignment _ (ReadMem ip_addr _))
      | let (ip_base, ip_off) = asBaseOffset ip_addr
      , let (sp_base, sp_off) = asBaseOffset next_sp
      , (ip_base, ip_off) == (sp_base, sp_off + stack_adj) ->
        let isRetLoad stmt =
              case stmt of
                AssignStmt asgn
                  | Just Refl <- testEquality (assignId asgn) (assignId  asgn) -> True
                _ -> False
         in Just $ filter (not . isRetLoad) stmts
    _ -> Nothing

-- | Return state post call
x86PostCallAbsState :: AbsBlockState X86Reg
                    -> MemSegmentOff 64
                    -> AbsBlockState X86Reg
x86PostCallAbsState =
  let params = CallParams { postCallStackDelta = 8
                          , preserveReg = \r -> Set.member (Some r) x86CalleeSavedRegs
                          }
   in absEvalCall params

freeBSD_syscallPersonality :: SyscallPersonality
freeBSD_syscallPersonality =
  SyscallPersonality { spTypeInfo = FreeBSD.syscallInfo
                     , spResultRegisters = [ Some RAX ]
                     }

x86DemandContext :: DemandContext X86_64
x86DemandContext =
  DemandContext { demandConstraints = \a -> a
                , archFnHasSideEffects = x86PrimFnHasSideEffects
                }

postX86TermStmtAbsState :: (forall tp . X86Reg tp -> Bool)
                        -> Memory 64
                        -> AbsBlockState X86Reg
                        -> RegState X86Reg (Value X86_64 ids)
                        -> X86TermStmt ids
                        -> Maybe (MemSegmentOff 64, AbsBlockState X86Reg)
postX86TermStmtAbsState preservePred mem s regs tstmt =
  case tstmt of
    X86Syscall ->
      case regs^.curIP of
        RelocatableValue _ addr | Just nextIP <- asSegmentOff mem addr -> do
          let params = CallParams { postCallStackDelta = 0
                                  , preserveReg = preservePred
                                  }
          Just (nextIP, absEvalCall params s nextIP)
        _ -> error $ "Sycall could not interpret next IP"


-- | Common architecture information for X86_64
x86_64_info :: (forall tp . X86Reg tp -> Bool)
               -- ^ Function that returns true if we should preserve a register across a system call.
            -> ArchitectureInfo X86_64
x86_64_info preservePred =
  ArchitectureInfo { withArchConstraints = \x -> x
                   , archAddrWidth      = Addr64
                   , archEndianness     = LittleEndian
                   , jumpTableEntrySize = 8
                   , disassembleFn      = disassembleBlockFromAbsState
                   , mkInitialAbsState = \_ addr -> initialX86AbsState addr
                   , absEvalArchFn     = transferAbsValue
                   , absEvalArchStmt   = \s _ -> s
                   , postCallAbsState = x86PostCallAbsState
                   , identifyCall      = identifyX86Call
                   , identifyReturn    = identifyX86Return
                   , rewriteArchFn     = rewriteX86PrimFn
                   , rewriteArchStmt   = rewriteX86Stmt
                   , rewriteArchTermStmt = rewriteX86TermStmt
                   , archDemandContext = x86DemandContext
                   , postArchTermStmtAbsState = postX86TermStmtAbsState preservePred
                   }

-- | Architecture information for X86_64 on FreeBSD.
x86_64_freeBSD_info :: ArchitectureInfo X86_64
x86_64_freeBSD_info = x86_64_info preserveFreeBSDSyscallReg

linux_syscallPersonality :: SyscallPersonality
linux_syscallPersonality =
  SyscallPersonality { spTypeInfo = Linux.syscallInfo
                     , spResultRegisters = [Some RAX]
                     }

-- | Architecture information for X86_64.
x86_64_linux_info :: ArchitectureInfo X86_64
x86_64_linux_info = x86_64_info preserveFn
  where preserveFn r = Set.member (Some r) linuxSystemCallPreservedRegisters
