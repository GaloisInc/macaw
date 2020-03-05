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
{-# LANGUAGE NondecreasingIndentation #-}
module Data.Macaw.X86
       ( x86_64_freeBSD_info
       , x86_64_linux_info
       , x86_64CallParams
       , freeBSD_syscallPersonality
       , linux_syscallPersonality
         -- * Low level exports
       , X86BlockPrecond(..)
       , ExploreLoc(..)
       , rootLoc
       , initX86State
       , tryDisassembleBlock
       , disassembleBlock
       , disassembleFixedBlock
       , translateInstruction
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

import           Control.Lens
import           Control.Monad.Cont
import           Control.Monad.Except
import           Control.Monad.ST
import           Data.Foldable
import qualified Data.Map as Map
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set
import qualified Data.Text as Text
import           Data.Word
import qualified Flexdis86 as F
import           Text.PrettyPrint.ANSI.Leijen (Pretty(..), text)

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types
  ( n8
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

-- | Information needed to disassble a This represents the control-flow information needed to build
-- basic blocks for a code location.
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
                 & curIP     .~ RelocatableValue Addr64 (segoffAddr (loc_ip loc))
                 & boundValue X87_TopReg .~ mkLit knownNat (toInteger (loc_x87_top loc))
                 & boundValue DF         .~ BoolValue (loc_df_flag loc)

------------------------------------------------------------------------
-- Location

-- | Describes the reason the translation error occured.
data X86TranslateError w
   = FlexdisMemoryError !(MemoryError w)
     -- ^ A memory error occured in decoding with Flexdis
   | DecodeError !(MemAddr w) !(InstructionDecodeError w)
     -- ^ A failure occured while trying to decode an instruction.
   | UnsupportedInstruction !(MemSegmentOff w) !F.InstructionInstance
     -- ^ The instruction is not supported by the translator
   | ExecInstructionError !(MemSegmentOff w) !F.InstructionInstance Text.Text
     -- ^ An error occured when trying to translate the instruction
   | UnexpectedTerminalInstruction !(MemSegmentOff w) !F.InstructionInstance

instance MemWidth w => Show (X86TranslateError w) where
  show err =
    case err of
      FlexdisMemoryError me ->
        show me
      DecodeError addr derr ->
        show addr ++ ": " ++ show derr
      UnsupportedInstruction addr i ->
        "Unsupported instruction at " ++ show addr ++ ": " ++ show i
      ExecInstructionError addr i msg ->
        "Error in interpreting instruction at " ++ show addr ++ ": " ++ show i ++ "\n  "
        ++ Text.unpack msg
      UnexpectedTerminalInstruction addr i -> do
        show addr ++ ": " ++ "Premature end of basic block due to instruction " ++ show i ++ "."


-- | Signal an error from the initial address.
initError :: RegState X86Reg (Value X86_64 ids)
          -> MemoryError 64
          -> Block X86_64 ids
initError s err =
  Block { blockStmts = []
        , blockTerm  = TranslateError s (Text.pack (show err))
        }

-- | Disassemble memory contents using flexdis.
disassembleInstruction :: MemSegmentOff 64
                          -- ^ Address of next instruction to disassemble
                       -> [MemChunk 64]
                          -- ^ Contents at address
                       -> ExceptT (X86TranslateError 64) (ST st_s) (F.InstructionInstance, Int, [MemChunk 64])
disassembleInstruction curIPAddr contents =
  case readInstruction contents of
    Left (errOff, err) -> do
      throwError $ DecodeError (segoffAddr curIPAddr & incAddr (toInteger errOff)) err
    Right r -> do
      pure r

-- | Translate block, returning blocks read, ending
-- PC, and an optional error.  and ending PC.
translateStep :: forall st_s ids
                     .  NonceGenerator (ST st_s) ids
                        -- ^ Generator for new assign ids
                     -> PreBlock ids
                        -- ^ Block information built up so far.
                     -> MemWord 64
                        -- ^ Offset of instruction from start of block
                     -> MemSegmentOff 64
                        -- ^ Address of next instruction to translate
                     -> [MemChunk 64]
                        -- ^ List of contents to read next.
                     -> ExceptT (X86TranslateError 64) (ST st_s)
                          (F.InstructionInstance, PartialBlock ids, Int, MemAddr 64, [MemChunk 64])
translateStep gen pblock blockOff curIPAddr contents = do
  (i, instSize, nextContents) <- disassembleInstruction curIPAddr contents
  -- Get size of instruction
  let next_ip :: MemAddr 64
      next_ip = segoffAddr curIPAddr & incAddr (toInteger instSize)
  let next_ip_val :: BVValue X86_64 ids 64
      next_ip_val = RelocatableValue Addr64 next_ip
  case execInstruction (ValueExpr next_ip_val) i of
    Nothing -> do
      throwError $ UnsupportedInstruction curIPAddr i
    Just exec -> do
      let gs = GenState { assignIdGen = gen
                        , _blockState = pblock
                        , genInitPCAddr = curIPAddr
                        , genInstructionSize = instSize
                        , avxMode = False
                        , _genRegUpdates = MapF.empty
                        }
      let transExcept msg = ExecInstructionError curIPAddr i msg
      res <-
        withExceptT transExcept $ runX86Generator gs $ do
          let line = Text.pack $ show $ F.ppInstruction i
          addStmt $ InstructionStart blockOff line
          asAtomicStateUpdate (MM.segoffAddr curIPAddr) exec
      pure $ (i, res, instSize, next_ip, nextContents)

-- | Recursive function used by `disassembleFixedBlock` below.
translateFixedBlock' :: NonceGenerator (ST st_s) ids
                       -> PreBlock ids
                       -> MemWord 64
                          -- ^ Offset relative to start of block.
                       -> MemSegmentOff 64
                       -- ^ Address of next instruction to translate
                       -> [MemChunk 64]
                       -- ^ List of contents to read next.
                       -> ExceptT (X86TranslateError 64) (ST st_s) (Block X86_64 ids)
translateFixedBlock' gen pblock blockOff curIPAddr contents = do
  (i, res, instSize, nextIP, nextContents) <- translateStep gen pblock blockOff curIPAddr contents
  let blockOff' = blockOff + fromIntegral instSize
  case unfinishedAtAddr res nextIP of
    Just pblock'
      | not (null nextContents)
      , Just nextIPAddr <- incSegmentOff curIPAddr (toInteger instSize) -> do
          translateFixedBlock' gen pblock' blockOff' nextIPAddr nextContents
    _  -> do
      when (not (null nextContents)) $ do
        throwError $ UnexpectedTerminalInstruction curIPAddr i
      pure $! finishPartialBlock res

{-# DEPRECATED disassembleFixedBlock "Planned for removal." #-}

-- | Disassemble a block with a fixed number of bytes.
disassembleFixedBlock :: NonceGenerator (ST st_s) ids
                      -> ExploreLoc
                         -- ^ Information about starting location for disassembling.
                      -> Int
                       -- ^ Number of bytes to translate
                      -> ST st_s (Either (X86TranslateError 64) (Block X86_64 ids))
disassembleFixedBlock gen loc sz = do
  let addr = loc_ip loc
  let initRegs = initX86State loc
  case segoffContentsAfter addr of
    Left err -> do
      pure $ Left $ FlexdisMemoryError err
    Right fullContents ->
      case splitMemChunks fullContents sz of
        Left _err -> do
          error $ "Could not split memory."
        Right (contents,_) -> do
          let pblock = emptyPreBlock addr initRegs
          runExceptT $ translateFixedBlock' gen pblock 0 addr contents

-- | Attempt to translate a single instruction into a Macaw block and instruction size.
translateInstruction :: NonceGenerator (ST st_s) ids
                     -> RegState X86Reg (Value X86_64 ids)
                          -- ^ Registers
                     -> MemSegmentOff 64
                        -- ^ Address of instruction to disassemble.
                     -> ExceptT (X86TranslateError 64) (ST st_s) (Block X86_64 ids, MemWord 64)
translateInstruction gen initRegs addr =
  case segoffContentsAfter addr of
    Left err -> do
      throwError $ FlexdisMemoryError err
    Right contents -> do
      let pblock = emptyPreBlock addr initRegs
      (_i, res, instSize, _nextIP, _nextContents) <- translateStep gen pblock 0 addr contents
      pure $! (finishPartialBlock res, fromIntegral instSize)

-- | Translate block, returning block read, number of bytes in block,
-- remaining bytes to parse, and an optional error.
translateBlockImpl :: forall st_s ids
                     .  NonceGenerator (ST st_s) ids
                        -- ^ Generator for new assign ids
                     -> PreBlock ids
                        -- ^ Block information built up so far.
                     -> MemSegmentOff 64
                        -- ^ Address of next instruction to translate
                     -> MemWord 64
                        -- ^ Offset of instruction from start of block
                     -> MemWord 64
                         -- ^ Maximum offset for this addr from start of block.
                     -> [MemChunk 64]
                        -- ^ List of contents to read next.
                     -> ST st_s ( Block X86_64 ids
                                , MemWord 64
                                )
translateBlockImpl gen pblock curIPAddr blockOff maxSize contents = do
  r <- runExceptT $ translateStep gen pblock blockOff curIPAddr contents
  case r of
    Left err -> do
      let b = Block { blockStmts = toList (pblock^.pBlockStmts)
                    , blockTerm  = TranslateError (pblock^.pBlockState) (Text.pack (show err))
                    }
      pure (b, blockOff)
    Right (_, res, instSize, nextIP, nextContents) -> do
      let blockOff' = blockOff + fromIntegral instSize
      case unfinishedAtAddr res nextIP of
        Just pblock'
          | blockOff' < maxSize
          , Just nextIPSegOff <- incSegmentOff curIPAddr (toInteger instSize) -> do
              translateBlockImpl gen pblock' nextIPSegOff blockOff' maxSize nextContents
        _ ->
          pure (finishPartialBlock res, blockOff')

-- | The abstract state for a function begining at a given address.
initialX86AbsState :: MemSegmentOff 64 -> AbsBlockState X86Reg
initialX86AbsState addr =
  let m = MapF.fromList [ MapF.Pair X87_TopReg (FinSet (Set.singleton 7))
                        , MapF.Pair DF         (BoolConst False)
                        ]
   in fnStartAbsBlockState addr m [(0, StackEntry (BVMemRepr n8 LittleEndian) ReturnAddr)]

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
    ReadFSBase -> TopV
    ReadGSBase -> TopV
    GetSegmentSelector _ -> TopV
    CPUID _    -> TopV
    CMPXCHG8B{} -> TopV
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
    X86IDivRem{} -> TopV
    X86DivRem{}  -> TopV
    SSE_UnaryOp{}  -> TopV
    SSE_VectorOp{}  -> TopV
    SSE_Sqrt{}  -> TopV
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

-- | Extra constraints on block for disassembling.
data X86BlockPrecond = X86BlockPrecond { blockInitX87TopReg :: !Word8
                                         -- ^ Value to assign to X87 Top register
                                         --
                                         -- (should be from 0 to 7 with 7 the stack is empty.)
                                       , blockInitDF :: !Bool
                                       }

type instance ArchBlockPrecond X86_64 = X86BlockPrecond

-- | Disassemble block, returning either an error, or a list of blocks
-- and ending PC.
extractX86BlockPrecond :: MemSegmentOff 64
                       -- ^ Address to disassemble at
                       -> AbsBlockState X86Reg
                       -- ^ Abstract state of processor for defining state.
                       -> Either String X86BlockPrecond
extractX86BlockPrecond _addr ab = do
  t <-
    case asConcreteSingleton (ab^.absRegState^.boundValue X87_TopReg) of
      Nothing -> Left "Could not determine height of X87 stack."
      Just t -> pure t
  d <-
    case ab^.absRegState^.boundValue DF of
      BoolConst b -> pure b
      _ -> Left $ "Could not determine df flag " ++ show (ab^.absRegState^.boundValue DF)
  pure $! X86BlockPrecond { blockInitX87TopReg = fromIntegral t
                          , blockInitDF = d
                          }

-- | Create initial registers for a block from address and preconditions.
initX86BlockRegs :: forall ids
                 .  MemSegmentOff 64
                 -- ^ Address to disassemble at
                 -> X86BlockPrecond
                 -- ^ Preconditions
                 -> RegState X86Reg (Value X86_64 ids)
initX86BlockRegs addr pr =
  let mkReg :: X86Reg tp -> Value X86_64 ids tp
      mkReg r
        | Just Refl <- testEquality r X86_IP =
            RelocatableValue Addr64 (segoffAddr addr)
        | Just Refl <- testEquality r X87_TopReg =
            mkLit knownNat (toInteger (blockInitX87TopReg pr))
        | Just Refl <- testEquality r DF =
            BoolValue (blockInitDF pr)
        | otherwise = Initial r
   in mkRegState mkReg

-- | Generate a Macaw block starting from the given address.
--
-- This is used in the architectur einfo.
translateBlockWithRegs :: forall s ids
                         .  NonceGenerator (ST s) ids
                            -- ^ Generator for creating fresh @AssignId@ values.
                         -> MemSegmentOff 64
                            -- ^ Address to disassemble at.
                         -> RegState X86Reg (Value X86_64 ids)
                            -- ^ Initial register values.
                         -> Int
                            -- ^ Maximum size of this block
                         -> ST s (Block X86_64 ids, Int)
translateBlockWithRegs gen addr initRegs maxSize = do
  case segoffContentsAfter addr of
    Left err -> do
      pure $! (initError initRegs err, 0)
    Right contents -> do
      (b, sz) <- translateBlockImpl gen (emptyPreBlock addr initRegs) addr 0 (fromIntegral maxSize) contents
      pure $! (b, fromIntegral sz)

-- | Attempt to identify the write to a stack return address, returning
-- instructions prior to that write and return  values.
--
-- This can also return Nothing if the call is not supported.
identifyX86Call :: Memory 64
                -> Seq (Stmt X86_64 ids)
                -> RegState X86Reg (Value X86_64 ids)
                -> Maybe (Seq (Stmt X86_64 ids), MemSegmentOff 64)
identifyX86Call mem stmts0 s = go stmts0 Seq.empty
  where -- Get value of stack pointer
        next_sp = s^.boundValue RSP
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
              , segmentFlags (segoffSegment ret_addr) `Perm.hasPerm` Perm.execute ->
                Just (prev Seq.>< after, ret_addr)
                -- Stop if we hit any architecture specific instructions prior to
                -- identifying return address since they may have side effects.
              | ExecArchStmt _ <- stmt -> Nothing
                -- Otherwise skip over this instruction.
              | otherwise -> go prev (stmt Seq.<| after)

-- | Return true if stack pointer has been reset to original value, and
-- return address is on top of stack.
checkForReturnAddrX86 :: forall ids
                      .  AbsProcessorState X86Reg ids
                      -> Bool
checkForReturnAddrX86 absState
  | Just (StackEntry _ ReturnAddr) <- Map.lookup 0 (absState^.curAbsStack) =
      True
  | otherwise =
      False

-- | Called to determine if the instruction sequence contains a return
-- from the current function.
--
-- An instruction executing a return from a function will place the
-- ReturnAddr value (placed on the top of the stack by
-- 'initialX86AbsState' above) into the instruction pointer.
identifyX86Return :: Seq (Stmt X86_64 ids)
                  -> RegState X86Reg (Value X86_64 ids)
                  -> AbsProcessorState X86Reg ids
                  -> Maybe (Seq (Stmt X86_64 ids))
identifyX86Return stmts s finalRegSt8 =
  case transferValue finalRegSt8 (s^.boundValue ip_reg) of
    ReturnAddr -> Just stmts
    _ -> Nothing

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

-- | Get the next IP that may run after this terminal and the abstract
-- state denoting possible starting conditions when that code runs.
postX86TermStmtAbsState :: (forall tp . X86Reg tp -> Bool)
                        -> Memory 64
                        -> AbsProcessorState X86Reg ids
                        -> Jmp.IntraJumpBounds X86_64 ids
                        -> RegState X86Reg (Value X86_64 ids)
                        -> X86TermStmt ids
                        -> Maybe ( MemSegmentOff 64
                                 , AbsBlockState X86Reg
                                 , Jmp.InitJumpBounds X86_64
                                 )
postX86TermStmtAbsState preservePred mem s bnds regs tstmt =
  case tstmt of
    X86Syscall ->
      case regs^.curIP of
        RelocatableValue _ addr | Just nextIP <- asSegmentOff mem addr -> do
          let params = CallParams { postCallStackDelta = 0
                                  , preserveReg = preservePred
                                  , stackGrowsDown = True
                                  }
          Just ( nextIP
               , absEvalCall params s regs nextIP
               , Jmp.postCallBounds params bnds regs
               )
        _ -> error $ "Sycall could not interpret next IP"
    Hlt ->
      Nothing
    UD2 ->
      Nothing

x86_64CallParams :: CallParams X86Reg
x86_64CallParams =
  CallParams { postCallStackDelta = 8
             , preserveReg = \r -> Set.member (Some r) x86CalleeSavedRegs
             , stackGrowsDown = True
             }


-- | Common architecture information for X86_64
x86_64_info :: (forall tp . X86Reg tp -> Bool)
               -- ^ Function that returns true if we should preserve a register across a system call.
            -> ArchitectureInfo X86_64
x86_64_info preservePred =
  ArchitectureInfo { withArchConstraints = \x -> x
                   , archAddrWidth = Addr64
                   , archEndianness = LittleEndian
                   , extractBlockPrecond = extractX86BlockPrecond
                   , initialBlockRegs = initX86BlockRegs
                   , disassembleFn  = translateBlockWithRegs
                   , mkInitialAbsState = \_ addr -> initialX86AbsState addr
                   , absEvalArchFn = transferAbsValue
                   , absEvalArchStmt = \s _ -> s
                   , identifyCall = identifyX86Call
                   , archCallParams = x86_64CallParams
                   , checkForReturnAddr = \_ s -> checkForReturnAddrX86 s
                   , identifyReturn = identifyX86Return
                   , rewriteArchFn = rewriteX86PrimFn
                   , rewriteArchStmt = rewriteX86Stmt
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


{-# DEPRECATED disassembleBlock "Use disassembleFn x86_64_info" #-}

-- | Disassemble block starting from explore location, and
-- return block along with size of block.
disassembleBlock :: forall s
                 .  NonceGenerator (ST s) s
                 -> ExploreLoc
                 -> MemWord 64
                    -- ^ Maximum number of bytes in ths block.
                 -> ST s (Block X86_64 s, MemWord 64)
disassembleBlock gen loc maxSize = do
  let addr = loc_ip loc
  let regs = initX86State loc
  let maxInt = toInteger (maxBound :: Int)
  let maxSizeFixed = fromIntegral $ min maxInt (toInteger maxSize)
  (b,sz) <- translateBlockWithRegs gen addr regs maxSizeFixed
  pure (b, fromIntegral sz)

{-# DEPRECATED tryDisassembleBlock "Use disassembleFn x86_64_info" #-}

-- | Disassemble block, returning either an error, or a list of blocks
-- and ending PC.
tryDisassembleBlock :: forall s ids
                    .  NonceGenerator (ST s) ids
                    -> MemSegmentOff 64
                       -- ^ Address to disassemble at
                    -> RegState X86Reg (Value X86_64 ids)
                       -- ^ Initial registers
                    -> Int
                       -- ^ Maximum size of this block
                    -> ExceptT String (ST s) (Block X86_64 ids, Int, Maybe String)
tryDisassembleBlock gen addr initRegs maxSize = lift $ do
  (b,sz) <- translateBlockWithRegs gen addr initRegs maxSize
  pure (b, sz, Nothing)
