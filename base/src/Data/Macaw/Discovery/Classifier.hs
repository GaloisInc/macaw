{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeApplications #-}
-- | Definitions supporting block classification during code discovery
--
-- This module defines data types and helpers to build block control flow
-- classifiers.  It comes with a pre-defined set that work well for most
-- architectures.  A reasonable default classifier is provided for all supported
-- architectures.  This infrastructure is available to enable derived tools to
-- customize code discovery heuristics, and to enable architectures to provide
-- architecture-specific rules.
--
-- Note that this is necessary for generating architecture-specific block
-- terminators that can only be correctly injected based on analysis of values
-- after abstract interpretation is applied to the rest of the code.
module Data.Macaw.Discovery.Classifier (
  -- * Utilities
    isExecutableSegOff
  , identifyConcreteAddresses
  -- * Pre-defined classifiers
  , branchClassifier
  , callClassifier
  , returnClassifier
  , directJumpClassifier
  , noreturnCallClassifier
  , tailCallClassifier
  -- * Reusable helpers
  , branchBlockState
  , classifierEndBlock
  ) where

import           Control.Applicative ( Alternative(empty) )
import           Control.Lens ( (^.), (&), (.~) )
import           Control.Monad ( when, unless )
import qualified Control.Monad.Reader as CMR
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Maybe ( maybeToList )
import qualified Data.Set as Set
import           Text.Printf (printf)

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import qualified Data.Macaw.AbsDomain.Refine as Refine
import           Data.Macaw.Architecture.Info as Info
import           Data.Macaw.CFG
import qualified Data.Macaw.Discovery.AbsEval as AbsEval
import qualified Data.Macaw.Discovery.ParsedContents as Parsed
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

------------------------------------------------------------------------
-- Utilities

isExecutableSegOff :: MemSegmentOff w -> Bool
isExecutableSegOff sa =
  segmentFlags (segoffSegment sa) `Perm.hasPerm` Perm.execute

-- | Get code pointers out of a abstract value.
identifyConcreteAddresses :: MemWidth w
                          => Memory w
                          -> AbsValue w (BVType w)
                          -> [MemSegmentOff w]
identifyConcreteAddresses mem (FinSet s) =
  let ins o r =
        case resolveAbsoluteAddr mem (fromInteger o) of
          Just a | isExecutableSegOff a -> a : r
          _ -> r
   in foldr ins [] s
identifyConcreteAddresses _ (CodePointers s _) = filter isExecutableSegOff $ Set.toList s
identifyConcreteAddresses _mem StridedInterval{} = []
identifyConcreteAddresses _mem _ = []


-- | @normBool b q@ returns a pair where for each `NotApp` applied to @b@, we recursively
-- take the argument to `NotApp` and the Boolean.
--
-- This is used to compare if one value is equal to or the syntactic
-- complement of another value.
normBool :: Value arch ids BoolType -> Bool -> (Value arch ids BoolType, Bool)
normBool x b
  | AssignedValue a <- x
  , EvalApp (NotApp xn) <- assignRhs a =
      normBool xn (not b)
  | otherwise = (x,b)

-- | This computes the abstract state for the start of a block for a
-- given branch target.  It is used so that we can make use of the
-- branch condition to simplify the abstract state.
branchBlockState :: forall a ids t
               .  ( Foldable t
                  )
               => Info.ArchitectureInfo a
               -> AbsProcessorState (ArchReg a) ids
               -> t (Stmt a ids)
               -> RegState (ArchReg a) (Value a ids)
                  -- ^  Register values
               -> Value a ids BoolType
                  -- ^ Branch condition
               -> Bool
                  -- ^ Flag indicating if branch is true or false.
               -> AbsBlockState (ArchReg a)
branchBlockState ainfo ps0 stmts regs c0 isTrue0 =
  Info.withArchConstraints ainfo $
    let (c,isTrue) = normBool c0 isTrue0
        ps = Refine.refineProcState c isTrue ps0
        mapReg :: ArchReg a tp -> Value a ids tp -> Value a ids tp
        mapReg _r v
          | AssignedValue a <- v
          , EvalApp (Mux _ cv0 tv fv) <- assignRhs a
          , (cv, b) <- normBool cv0 isTrue
          , cv == c =
              if b then tv else fv
          | otherwise =
              v
        refinedRegs = mapRegsWith mapReg regs
     in finalAbsBlockState (F.foldl' (AbsEval.absEvalStmt ainfo) ps stmts) refinedRegs

classifyDirectJump :: RegisterInfo (ArchReg arch)
                   => ParseContext arch ids
                   -> String
                   -> Value arch ids (BVType (ArchAddrWidth arch))
                   -> BlockClassifierM arch ids (MemSegmentOff (ArchAddrWidth arch))
classifyDirectJump ctx nm v = do
  ma <- case valueAsMemAddr v of
          Nothing ->  fail $ nm ++ " value " ++ show v ++ " is not a valid address."
          Just a -> pure a
  a <- case asSegmentOff (pctxMemory ctx) ma of
         Nothing ->
           fail $ nm ++ " value " ++ show v ++ " is not a segment offset in " ++ show (pctxMemory ctx) ++ "."
         Just sa -> pure sa
  when (not (segmentFlags (segoffSegment a) `Perm.hasPerm` Perm.execute)) $ do
    fail $ nm ++ " value " ++ show a ++ " is not executable."
  when (a == pctxFunAddr ctx) $ do
    fail $ nm ++ " value " ++ show a ++ " refers to function start."
  when (a `Map.member` pctxKnownFnEntries ctx) $ do
    fail $ nm ++ " value " ++ show a ++ " is a known function entry."
  pure a

-- | The classifier for conditional and unconditional branches
--
-- Note that this classifier can convert a conditional branch to an
-- unconditional branch if (and only if) the condition is syntactically true or
-- false after constant propagation. It never attempts sophisticated path
-- trimming.
branchClassifier :: BlockClassifier arch ids
branchClassifier = classifierName "Branch" $ do
  bcc <- CMR.ask
  let ctx = classifierParseContext bcc
  let finalRegs = classifierFinalRegState bcc
  let writtenAddrs = classifierWrittenAddrs bcc
  let absState = classifierAbsState bcc
  let stmts = classifierStmts bcc
  let ainfo = pctxArchInfo ctx
  Info.withArchConstraints ainfo $ do
    -- The block ends with a Mux, so we turn this into a `ParsedBranch` statement.
    let ipVal = finalRegs^.boundValue ip_reg
    (c,t,f) <- case valueAsApp ipVal of
                 Just (Mux _ c t f) -> pure (c,t,f)
                 _ -> fail $ "IP is not an mux:\n"
                          ++ show (ppValueAssignments ipVal)
    trueTgtAddr  <- classifyDirectJump ctx "True branch"  t
    falseTgtAddr <- classifyDirectJump ctx "False branch" f

    let trueRegs  = finalRegs & boundValue ip_reg .~ t
    let falseRegs = finalRegs & boundValue ip_reg .~ f

    let trueAbsState  = branchBlockState ainfo absState stmts trueRegs c True
    let falseAbsState = branchBlockState ainfo absState stmts falseRegs c False
    let jmpBounds = classifierJumpBounds bcc
    case Jmp.postBranchBounds jmpBounds finalRegs c of
      Jmp.BothFeasibleBranch trueJmpState falseJmpState -> do
        pure $ Parsed.ParsedContents { Parsed.parsedNonterm = F.toList stmts
                                  , Parsed.parsedTerm  =
                                    Parsed.ParsedBranch finalRegs c trueTgtAddr falseTgtAddr
                                  , Parsed.writtenCodeAddrs = writtenAddrs
                                  , Parsed.intraJumpTargets =
                                    [ (trueTgtAddr,  trueAbsState,  trueJmpState)
                                    , (falseTgtAddr, falseAbsState, falseJmpState)
                                    ]
                                  , Parsed.newFunctionAddrs = []
                                  }
      -- The false branch is impossible.
      Jmp.TrueFeasibleBranch trueJmpState -> do
        pure $ Parsed.ParsedContents { Parsed.parsedNonterm = F.toList stmts
                                  , Parsed.parsedTerm  = Parsed.ParsedJump finalRegs trueTgtAddr
                                  , Parsed.writtenCodeAddrs = writtenAddrs
                                  , Parsed.intraJumpTargets =
                                    [(trueTgtAddr, trueAbsState, trueJmpState)]
                                  , Parsed.newFunctionAddrs = []
                                  }
      -- The true branch is impossible.
      Jmp.FalseFeasibleBranch falseJmpState -> do
        pure $ Parsed.ParsedContents { Parsed.parsedNonterm = F.toList stmts
                                  , Parsed.parsedTerm  = Parsed.ParsedJump finalRegs falseTgtAddr
                                  , Parsed.writtenCodeAddrs = writtenAddrs
                                  , Parsed.intraJumpTargets =
                                    [(falseTgtAddr, falseAbsState, falseJmpState)]
                                  , Parsed.newFunctionAddrs = []
                              }
      -- Both branches were deemed impossible
      Jmp.InfeasibleBranch -> do
        fail $ "Branch targets are both unreachable."

-- | Identify new potential function entry points by looking at IP.
identifyCallTargets :: forall arch ids
                    .  (RegisterInfo (ArchReg arch))
                    => Memory (ArchAddrWidth arch)
                    -> AbsProcessorState (ArchReg arch) ids
                       -- ^ Abstract processor state just before call.
                    -> RegState (ArchReg arch) (Value arch ids)
                    -> [ArchSegmentOff arch]
identifyCallTargets mem absState regs = do
  -- Code pointers from abstract domains.
  let def = identifyConcreteAddresses mem $ transferValue absState (regs^.boundValue ip_reg)
  case regs^.boundValue ip_reg of
    BVValue _ x ->
      maybeToList $ resolveAbsoluteAddr mem (fromInteger x)
    RelocatableValue _ a ->
      maybeToList $ asSegmentOff mem a
    SymbolValue{} -> []
    AssignedValue a ->
      case assignRhs a of
        -- See if we can get a value out of a concrete memory read.
        ReadMem addr (BVMemRepr _ end)
          | Just laddr <- valueAsMemAddr addr
          , Right val <- readSegmentOff mem end laddr ->
            val : def
        _ -> def
    Initial _ -> def

-- |  Use the architecture-specific callback to check if last statement was a call.
--
-- Note that in some cases the call is known not to return, and thus this code
-- will never jump to the return value; in that case, the
-- 'noreturnCallClassifier' should fire. As such, 'callClassifier' should always
-- be attempted *after* 'noreturnCallClassifier'.
callClassifier :: BlockClassifier arch ids
callClassifier = do
  bcc <- CMR.ask
  let ctx = classifierParseContext bcc
  let finalRegs = classifierFinalRegState bcc
  let ainfo = pctxArchInfo ctx
  let mem = pctxMemory ctx
  ret <- case Info.identifyCall ainfo mem (classifierStmts bcc) finalRegs of
           Just (_prev_stmts, ret) -> pure ret
           Nothing -> fail $ "Call classifer failed."
  Info.withArchConstraints ainfo $ do
    pure $ Parsed.ParsedContents { Parsed.parsedNonterm = F.toList (classifierStmts bcc)
                              , Parsed.parsedTerm  = Parsed.ParsedCall finalRegs (Just ret)
                              -- The return address may be written to
                              -- stack, but is highly unlikely to be
                              -- a function entry point.
                              , Parsed.writtenCodeAddrs = filter (\a -> a /= ret) (classifierWrittenAddrs bcc)
                              --Include return target
                              , Parsed.intraJumpTargets =
                                [( ret
                                 , Info.postCallAbsState ainfo (classifierAbsState bcc) finalRegs ret
                                 , Jmp.postCallBounds (Info.archCallParams ainfo) (classifierJumpBounds bcc) finalRegs
                                 )]
                              -- Use the abstract domain to look for new code pointers for the current IP.
                              , Parsed.newFunctionAddrs = identifyCallTargets mem (classifierAbsState bcc) finalRegs
                              }

-- | Check this block ends with a return as identified by the
-- architecture-specific processing.  Basic return identification
-- can be performed by detecting when the Instruction Pointer
-- (ip_reg) contains the 'ReturnAddr' symbolic value (initially
-- placed on the top of the stack or in the Link Register by the
-- architecture-specific state initializer).  However, some
-- architectures perform expression evaluations on this value before
-- loading the IP (e.g. ARM will clear the low bit in T32 mode or
-- the low 2 bits in A32 mode), so the actual detection process is
-- deferred to architecture-specific functionality.
returnClassifier :: BlockClassifier arch ids
returnClassifier = classifierName "Return" $ do
  bcc <- CMR.ask
  let ainfo = pctxArchInfo (classifierParseContext bcc)
  Info.withArchConstraints ainfo $ do
    Just prevStmts <-
      pure $ Info.identifyReturn ainfo
                            (classifierStmts bcc)
                            (classifierFinalRegState bcc)
                            (classifierAbsState bcc)
    pure $ Parsed.ParsedContents { Parsed.parsedNonterm = F.toList prevStmts
                              , Parsed.parsedTerm = Parsed.ParsedReturn (classifierFinalRegState bcc)
                              , Parsed.writtenCodeAddrs = classifierWrittenAddrs bcc
                              , Parsed.intraJumpTargets = []
                              , Parsed.newFunctionAddrs = []
                              }

-- | Classifies jumps to concrete addresses as unconditional jumps.  Note that
-- this logic is substantially similar to the 'callClassifier'; as such, this
-- classifier should always be applied *after* the 'callClassifier'.
directJumpClassifier :: BlockClassifier arch ids
directJumpClassifier = classifierName "Jump" $ do
  bcc <- CMR.ask
  let ctx = classifierParseContext bcc
  let ainfo = pctxArchInfo ctx
  Info.withArchConstraints ainfo $ do

    tgtMSeg <- classifyDirectJump ctx "Jump" (classifierFinalRegState bcc ^. boundValue ip_reg)

    let abst = finalAbsBlockState (classifierAbsState bcc) (classifierFinalRegState bcc)
    let abst' = abst & setAbsIP tgtMSeg
    let tgtBnds = Jmp.postJumpBounds (classifierJumpBounds bcc) (classifierFinalRegState bcc)
    pure $ Parsed.ParsedContents { Parsed.parsedNonterm = F.toList (classifierStmts bcc)
                              , Parsed.parsedTerm  = Parsed.ParsedJump (classifierFinalRegState bcc) tgtMSeg
                              , Parsed.writtenCodeAddrs = classifierWrittenAddrs bcc
                              , Parsed.intraJumpTargets = [(tgtMSeg, abst', tgtBnds)]
                              , Parsed.newFunctionAddrs = []
                              }

classifierEndBlock :: BlockClassifierContext arch ids
                   -> MemAddr (ArchAddrWidth arch)
classifierEndBlock ctx = Info.withArchConstraints (pctxArchInfo (classifierParseContext ctx)) $
  let blockStart = segoffAddr (pctxAddr (classifierParseContext ctx))
   in incAddr (toInteger (classifierBlockSize ctx)) blockStart

noreturnCallParsedContents :: BlockClassifierContext arch ids -> Parsed.ParsedContents arch ids
noreturnCallParsedContents bcc =
  let ctx  = classifierParseContext bcc
      mem  = pctxMemory ctx
      absState = classifierAbsState bcc
      regs = classifierFinalRegState bcc
      blockEnd = classifierEndBlock bcc
   in Info.withArchConstraints (pctxArchInfo ctx) $
        Parsed.ParsedContents { Parsed.parsedNonterm = F.toList (classifierStmts bcc)
                           , Parsed.parsedTerm  = Parsed.ParsedCall regs Nothing
                           , Parsed.writtenCodeAddrs =
                             filter (\a -> segoffAddr a /= blockEnd) $
                             classifierWrittenAddrs bcc
                           , Parsed.intraJumpTargets = []
                           , Parsed.newFunctionAddrs = identifyCallTargets mem absState regs
                           }

-- | Attempt to recognize a call to a function that is known to not
-- return. These are effectively tail calls, even if the compiler did not
-- obviously generate a tail call instruction sequence.
--
-- This classifier is important because compilers often place garbage
-- instructions (for alignment, or possibly the next function) after calls to
-- no-return functions. Without knowledge of no-return functions, macaw would
-- otherwise think that the callee could return to the garbage instructions,
-- causing later classification failures.
--
-- This functionality depends on a set of known non-return functions are
-- specified as an input to the code discovery process (see 'pctxKnownFnEntries').
--
-- Note that this classifier should always be run before the 'callClassifier'.
noreturnCallClassifier :: BlockClassifier arch ids
noreturnCallClassifier = classifierName "no return call" $ do
  bcc <- CMR.ask
  let ctx = classifierParseContext bcc
  -- Check for tail call when the calling convention seems to be satisfied.
  Info.withArchConstraints (pctxArchInfo ctx) $ do
    let regs = classifierFinalRegState bcc
    let ipVal = regs ^. boundValue ip_reg
    -- Get memory address
    ma <-
      case valueAsMemAddr ipVal of
        Nothing ->  fail $ printf "Noreturn target %s is not a valid address." (show ipVal)
        Just a -> pure a
    -- Get address
    a <- case asSegmentOff (pctxMemory ctx) ma of
           Nothing ->
             fail $ printf "Noreturn target %s is not a segment offset." (show ipVal)
           Just sa -> pure sa
    -- Check function labeled noreturn
    case Map.lookup a (pctxKnownFnEntries ctx) of
      Nothing -> fail $ printf "Noreturn target %s is not a known function entry." (show a)
      Just MayReturnFun -> fail $ printf "Return target %s labeled mayreturn." (show a)
      Just NoReturnFun -> pure ()
    -- Return no
    pure $! noreturnCallParsedContents bcc

-- | Attempt to recognize tail call
--
-- The current heuristic is that the target looks like a call, except the stack
-- height in the caller is 0.
tailCallClassifier :: BlockClassifier arch ids
tailCallClassifier = classifierName "Tail call" $ do
  bcc <- CMR.ask
  let ctx = classifierParseContext bcc
  let ainfo = pctxArchInfo ctx
  -- Check for tail call when the calling convention seems to be satisfied.
  Info.withArchConstraints ainfo $ do

    let spVal = classifierFinalRegState bcc ^. boundValue sp_reg
    -- Check to see if the stack pointer points to an offset of the initial stack.
    o <-
      case transferValue (classifierAbsState bcc) spVal of
        StackOffsetAbsVal _ o -> pure o
        _ -> fail $ "Not a stack offset"
    -- Stack stack is back to height when function was called.
    unless (o == 0) $
      fail "Expected stack height of 0"
    -- Return address is pushed
    unless (Info.checkForReturnAddr ainfo (classifierFinalRegState bcc) (classifierAbsState bcc)) empty
    pure $! noreturnCallParsedContents bcc
