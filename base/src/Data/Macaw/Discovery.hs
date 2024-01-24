{-|
This module discovers the Functions and their internal Block CFG in
target binaries.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Discovery
       ( -- * DiscoveryInfo
         State.DiscoveryState(..)
       , State.emptyDiscoveryState
       , State.trustedFunctionEntryPoints
       , State.exploreFnPred
       , State.AddrSymMap
       , State.funInfo
       , State.exploredFunctions
       , State.ppDiscoveryStateBlocks
       , State.unexploredFunctions
       , Data.Macaw.Discovery.cfgFromAddrs
       , Data.Macaw.Discovery.cfgFromAddrsAndState
       , Data.Macaw.Discovery.markAddrAsFunction
       , Data.Macaw.Discovery.markAddrsAsFunction
       , State.FunctionExploreReason(..)
       , State.ppFunReason
       , State.BlockExploreReason(..)
       , Data.Macaw.Discovery.analyzeFunction
       , Data.Macaw.Discovery.analyzeDiscoveredFunctions
       , Data.Macaw.Discovery.addDiscoveredFunctionBlockTargets
       , Data.Macaw.Discovery.discoverFunction
         -- * Top level utilities
       , Data.Macaw.Discovery.completeDiscoveryState
       , Data.Macaw.Discovery.incCompleteDiscovery
       , DiscoveryOptions(..)
       , defaultDiscoveryOptions
       , DiscoveryEvent(..)
       , logDiscoveryEvent
         -- * DiscoveryFunInfo
       , State.DiscoveryFunInfo
       , State.discoveredFunAddr
       , State.discoveredFunName
       , State.discoveredFunSymbol
       , State.discoveredClassifyFailureResolutions
       , State.parsedBlocks
       , State.NoReturnFunStatus(..)
         -- * Parsed block
       , State.ParsedBlock
       , State.pblockAddr
       , State.blockSize
       , State.blockReason
       , State.blockAbstractState
       , State.pblockStmts
       , State.pblockTermStmt
       , State.ParsedTermStmt(..)
       , State.JumpTableLayout
       , State.jtlBackingAddr
       , State.jtlBackingSize
       -- * Block classifiers
       , BlockClassifier
       , defaultClassifier
       , branchClassifier
       , callClassifier
       , returnClassifier
       , directJumpClassifier
       , noreturnCallClassifier
       , tailCallClassifier
       , pltStubClassifier
       , jumpTableClassifier
         -- * Simplification
       , eliminateDeadStmts
       , identifyCallTargets
         -- * Re-exports
       , ArchAddrWidth
       ) where

import           Control.Applicative ( Alternative((<|>)) )
import           Control.Lens ( Lens', (&), (^.), (^?), (%~), (.~), (%=), use, lens, _Just, at )
import           Control.Monad ( unless, when )
import qualified Control.Monad.ST.Lazy as STL
import qualified Control.Monad.ST.Strict as STS
import qualified Control.Monad.State.Strict as CMS
import qualified Data.ByteString.Char8 as BSC
import qualified Data.Foldable as F
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe ( fromMaybe, maybeToList )
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.Nonce as PN
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Sequence as Seq
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Text as Text
import qualified System.IO as IO

#define USE_REWRITER

import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
#ifdef USE_REWRITER
import           Data.Macaw.CFG.Rewriter
#endif
import           Data.Macaw.DebugLogging
import           Data.Macaw.Discovery.AbsEval
import           Data.Macaw.Discovery.Classifier
import           Data.Macaw.Discovery.Classifier.JumpTable ( jumpTableClassifier )
import           Data.Macaw.Discovery.Classifier.PLT ( pltStubClassifier )
import           Data.Macaw.Discovery.ParsedContents
import           Data.Macaw.Discovery.State as State
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types
import           Data.Macaw.Utils.IncComp


{-
-- | Return true if this address was added because of the contents of a global address
-- in memory initially.
--
-- This heuristic is not very accurate, so we avoid printing errors when it leads to
-- issues.
cameFromUnsoundReason :: Map (ArchMemAddr arch) (FoundAddr arch)
                      -> CodeAddrReason (ArchAddrWidth arch)
                      -> Bool
cameFromUnsoundReason found_map rsn = do
  let prev addr =
        case Map.lookup addr found_map of
          Just info -> cameFromUnsoundReason found_map (foundReason info)
          Nothing -> error $ "Unknown reason for address " ++ show addr
  case rsn of
    InWrite{} -> True
    NextIP src  -> prev src
    CallTarget src -> prev src
    SplitAt src -> prev src
    InitAddr -> False
    CodePointerInMem{} -> True
-}

------------------------------------------------------------------------
-- Eliminate dead code in blocks

-- | Add any values needed to compute term statement to demand set.
addTermDemands :: TermStmt arch ids -> DemandComp arch ids ()
addTermDemands t =
  case t of
    FetchAndExecute regs -> do
      TF.traverseF_ addValueDemands regs
    TranslateError regs _ -> do
      TF.traverseF_ addValueDemands regs
    ArchTermStmt _ regs -> do
      TF.traverseF_ addValueDemands regs

-- | Add any assignments needed to evaluate statements with side
-- effects and terminal statement to demand set.
addBlockDemands :: Block arch ids -> DemandComp arch ids ()
addBlockDemands b = do
  mapM_ addStmtDemands (blockStmts b)
  addTermDemands (blockTerm b)

-- | Return a block after filtering out statements not needed to compute it.
elimDeadStmtsInBlock :: AssignIdSet ids -> Block arch ids -> Block arch ids
elimDeadStmtsInBlock demandSet b =
  b { blockStmts = filter (stmtNeeded demandSet) (blockStmts b)
    }

-- | Eliminate all dead statements in blocks
eliminateDeadStmts :: ArchitectureInfo arch -> Block arch ids -> Block arch ids
eliminateDeadStmts ainfo b = elimDeadStmtsInBlock demandSet b
  where demandSet =
          runDemandComp (archDemandContext ainfo) $ do
            addBlockDemands b

------------------------------------------------------------------------
-- Eliminate dead code in blocks

-- | Add any assignments needed to evaluate statements with side
-- effects and terminal statement to demand set.
addParsedBlockDemands :: ParsedBlock arch ids -> DemandComp arch ids ()
addParsedBlockDemands b = do
  mapM_ addStmtDemands (pblockStmts b)
  case pblockTermStmt b of
    ParsedCall regs _ -> do
      TF.traverseF_ addValueDemands regs
    PLTStub regs _ _ ->
      TF.traverseF_ addValueDemands regs
    ParsedJump regs _ -> do
      TF.traverseF_ addValueDemands regs
    ParsedBranch regs _ _ _ -> do
      TF.traverseF_ addValueDemands regs
    ParsedLookupTable _layout regs _idx _tbl  -> do
      TF.traverseF_ addValueDemands regs
    ParsedReturn regs -> do
      TF.traverseF_ addValueDemands regs
    ParsedArchTermStmt _ regs _ -> do
      TF.traverseF_ addValueDemands regs
    ParsedTranslateError _ -> do
      pure ()
    ClassifyFailure regs _ -> do
      TF.traverseF_ addValueDemands regs

-- | Eliminate all dead statements in blocks
dropUnusedCodeInParsedBlock :: ArchitectureInfo arch
                            -> ParsedBlock arch ids
                            -> ParsedBlock arch ids
dropUnusedCodeInParsedBlock ainfo b =
    -- Important to force the result list here, since otherwise we
    -- hold onto the entire input list
    foldr seq () stmts' `seq` b { pblockStmts = stmts' }
  where stmts' = filter stmtPred (pblockStmts b)
        demandSet =
          runDemandComp (archDemandContext ainfo) $ do
            addParsedBlockDemands b
        stmtPred = stmtNeeded demandSet

------------------------------------------------------------------------
-- DiscoveryState utilities


-- | Return true if we should explore this function.
explorableFunction :: Memory w
                   -> (MemSegmentOff w -> Bool)
                   -> MemSegmentOff w
                   -> Bool
explorableFunction mem p addr
  | isExecutableSegOff addr
  , p addr =
    addrWidthClass (memAddrWidth mem) $
      -- We check that the function address ignores bytes so that we do
      -- not start disassembling at a relocation or BSS region.
      case segoffContentsAfter addr of
        Right (ByteRegion _:_) -> True
        _ -> False
  | otherwise = False

-- | Return true if we should explore this function.
shouldExploreFunction :: ArchSegmentOff arch
                      -> DiscoveryState arch
                      -> Bool
shouldExploreFunction addr s
  =  not (Map.member addr (s^.funInfo))
  && not (Map.member addr (s^.unexploredFunctions))
  && explorableFunction (memory s) (s^.exploreFnPred) addr

-- | Mark a escaped code pointer as a function entry.
markAddrAsFunction :: FunctionExploreReason (ArchAddrWidth arch)
                      -- ^ Information about why the code address was discovered
                      --
                      -- Used for debugging
                   -> ArchSegmentOff arch
                   -> DiscoveryState arch
                   -> DiscoveryState arch
markAddrAsFunction rsn addr s
  | shouldExploreFunction addr s =
    s & unexploredFunctions %~ Map.insert addr rsn
  | otherwise =
    s

-- | Mark a list of addresses as function entries with the same reason.
markAddrsAsFunction :: Foldable t
                    => FunctionExploreReason (ArchAddrWidth arch)
                    -> t (ArchSegmentOff arch)
                    -> DiscoveryState arch
                    -> DiscoveryState arch
markAddrsAsFunction rsn addrs s0 =
  let ins s a | shouldExploreFunction a s = s & unexploredFunctions %~ Map.insert a rsn
              | otherwise = s
   in F.foldl' ins s0 addrs


------------------------------------------------------------------------
-- FoundAddr

-- | An address that has been found to be reachable.
data FoundAddr arch
   = FoundAddr { foundReason :: !(BlockExploreReason (ArchAddrWidth arch))
                 -- ^ The reason the address was found to be containing code.
               , foundAbstractState :: !(AbsBlockState (ArchReg arch))
                 -- ^ The abstract state formed from post-states that reach this address.
               , foundJumpBounds :: !(Jmp.InitJumpBounds arch)
                 -- ^ The abstract state formed from post-states that reach this address
                 --
                 -- This is used for jump bounds.
               }

foundReasonL :: Lens' (FoundAddr arch) (BlockExploreReason (ArchAddrWidth arch))
foundReasonL = lens foundReason (\old new -> old { foundReason = new })

------------------------------------------------------------------------
-- FunState

-- | The state for the function exploration monad (funM)
data FunState arch s ids
   = FunState { funReason :: !(FunctionExploreReason (ArchAddrWidth arch))
              , funNonceGen  :: !(PN.NonceGenerator (STS.ST s) ids)
              , curFunAddr   :: !(ArchSegmentOff arch)
                -- ^ Address of the function
              , _curFunCtx   :: !(DiscoveryState arch)
                -- ^ Discovery state without this function
              , _curFunBlocks :: !(Map (ArchSegmentOff arch) (ParsedBlock arch ids))
                -- ^ Maps an address to the blocks associated with that address.
              , _foundAddrs :: !(Map (ArchSegmentOff arch) (FoundAddr arch))
                -- ^ Maps found address to the pre-state for that block.
              , _reverseEdges :: !(ReverseEdgeMap arch)
                -- ^ Maps each code address to the list of predecessors that
                -- affected its abstract state.
              , _frontier    :: !(Set (ArchSegmentOff arch))
                -- ^ Addresses to explore next.
              , _newEntries :: !(CandidateFunctionMap arch)
              , classifyFailureResolutions :: [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                -- ^ The first element of each pair is the block (ending in a
                -- 'ClassifyFailure') for which the second element provides a
                -- list of known jump targets. These inform the initial
                -- frontier, but also need to be preserved as a side mapping
                -- when we construct the 'DiscoveryFunInfo'.
                --
                -- These resolutions are provided by external data (e.g.,
                -- another code discovery engine or SMT) and help resolve
                -- control flow that macaw cannot understand.
              }

-- | Discovery info
curFunCtx :: Lens' (FunState arch s ids)  (DiscoveryState arch)
curFunCtx = lens _curFunCtx (\s v -> s { _curFunCtx = v })

-- | Information about current function we are working on
curFunBlocks :: Lens' (FunState arch s ids) (Map (ArchSegmentOff arch) (ParsedBlock arch ids))
curFunBlocks = lens _curFunBlocks (\s v -> s { _curFunBlocks = v })

foundAddrs :: Lens' (FunState arch s ids) (Map (ArchSegmentOff arch) (FoundAddr arch))
foundAddrs = lens _foundAddrs (\s v -> s { _foundAddrs = v })

newEntries :: Lens' (FunState arch s ids) (CandidateFunctionMap arch)
newEntries = lens _newEntries (\s v -> s { _newEntries = v })

-- | Add a block to the current function blocks. If this overlaps with an
-- existing block, split them so that there's no overlap.
addFunBlock
  :: MemWidth (ArchAddrWidth arch)
  => ArchSegmentOff arch
  -> ParsedBlock arch ids
  -> FunState arch s ids
  -> FunState arch s ids
addFunBlock segment block s =
  case Map.lookupLT segment (s ^. curFunBlocks) of
    Just (bSegment, bBlock)
        -- very sneaky way to check that they are in the same segment (a
        -- Nothing result from diffSegmentOff will never be greater than a
        -- Just) and that they are overlapping (the block size is bigger than
        -- you'd expect given the address difference)
        | diffSegmentOff bSegment segment > Just (-toInteger (blockSize bBlock))
        -- put the overlapped segment back in the frontier
        -> s & curFunBlocks %~ (Map.insert segment block . Map.delete bSegment)
             & foundAddrs.at bSegment._Just.foundReasonL %~ SplitAt segment
             & frontier %~ Set.insert bSegment
    _ -> s & curFunBlocks %~ Map.insert segment block

type ReverseEdgeMap arch = Map (ArchSegmentOff arch) (Set (ArchSegmentOff arch))

-- | Maps each code address to the list of predecessors that
-- affected its abstract state.
reverseEdges :: Lens' (FunState arch s ids) (ReverseEdgeMap arch)
reverseEdges = lens _reverseEdges (\s v -> s { _reverseEdges = v })

-- | Set of addresses to explore next.
--
-- This is a map so that we can associate a reason why a code address
-- was added to the frontier.
frontier :: Lens' (FunState arch s ids) (Set (ArchSegmentOff arch))
frontier = lens _frontier (\s v -> s { _frontier = v })

------------------------------------------------------------------------
-- FunM

-- | A newtype around a function
newtype FunM arch s ids a = FunM { unFunM :: CMS.StateT (FunState arch s ids) (STL.ST s) a }
  deriving (Functor, Applicative, Monad)

instance CMS.MonadState (FunState arch s ids) (FunM arch s ids) where
  get = FunM CMS.get
  put s = FunM $ CMS.put s

------------------------------------------------------------------------
-- Transfer functions

-- | Joins in the new abstract state and returns the locations for
-- which the new state is changed.
mergeIntraJump  :: ArchitectureInfo arch
                -> ArchSegmentOff arch
                  -- ^ Source label that we are jumping from.
                -> Jmp.IntraJumpTarget arch
                   -- ^ Target we are jumping to.
                -> FunM arch s ids ()
mergeIntraJump info src (tgt, ab, bnds) = do
  withArchConstraints info $ do
   unless (absStackHasReturnAddr ab) $ do
    debug DCFG ("WARNING: Missing return value in jump from " ++ show src ++ " to\n" ++ show ab) $
      pure ()
   -- Associate a new abstract state with the code region.
   foundMap <- use foundAddrs
   case Map.lookup tgt foundMap of
    -- We have seen this block before, so need to join and see if
    -- the results is changed.
    Just old_info -> do
      case joinAbsBlockState (foundAbstractState old_info) ab of
        Nothing  -> return ()
        Just new -> do
          let new_info = old_info { foundAbstractState = new }
          foundAddrs   %= Map.insert tgt new_info
          reverseEdges %= Map.insertWith Set.union tgt (Set.singleton src)
          frontier %= Set.insert tgt
    -- We haven't seen this block before
    Nothing -> do
      reverseEdges %= Map.insertWith Set.union tgt (Set.singleton src)
      frontier     %= Set.insert tgt
      let foundInfo = FoundAddr { foundReason = NextIP src
                                , foundAbstractState = ab
                                , foundJumpBounds = bnds
                                }
      foundAddrs %= Map.insert tgt foundInfo


------------------------------------------------------------------------
-- recordWriteStmts

-- | Mark addresses written to memory that point to code as function
-- entry points.
recordWriteStmts :: ArchitectureInfo arch
                 -> Memory (ArchAddrWidth arch)
                 -> AbsProcessorState (ArchReg arch) ids
                 -> [ArchSegmentOff arch]
                 -> [Stmt arch ids]
                 -> ( AbsProcessorState (ArchReg arch) ids
                    , [ArchSegmentOff arch]
                    )
recordWriteStmts _archInfo _mem absState writtenAddrs [] =
  seq absState (absState, writtenAddrs)
recordWriteStmts ainfo mem absState writtenAddrs (stmt:stmts) =
  seq absState $ do
    let absState' = absEvalStmt ainfo absState stmt
    let writtenAddrs' =
          case stmt of
            WriteMem _addr repr v
              | Just PC.Refl <- PC.testEquality repr (addrMemRepr ainfo) ->
                withArchConstraints ainfo $
                  let addrs = identifyConcreteAddresses mem (transferValue absState v)
                   in addrs ++ writtenAddrs
            _ ->
              writtenAddrs
    recordWriteStmts ainfo mem absState' writtenAddrs' stmts


-- | Get the memory representation associated with pointers in the
-- given architecture.
addrMemRepr :: ArchitectureInfo arch -> MemRepr (BVType (RegAddrWidth (ArchReg arch)))
addrMemRepr arch_info =
  case archAddrWidth arch_info of
    Addr32 -> BVMemRepr n4 (archEndianness arch_info)
    Addr64 -> BVMemRepr n8 (archEndianness arch_info)

useExternalTargets :: ( PC.OrdF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                   => BlockClassifierContext arch ids
                   -> Maybe [Jmp.IntraJumpTarget arch]
useExternalTargets bcc = do
  let ctx = classifierParseContext bcc
  let finalRegs = classifierFinalRegState bcc
  let jmpBounds = classifierJumpBounds bcc
  let absState = classifierAbsState bcc
  let initRegs = classifierInitRegState bcc
  let ipVal = initRegs ^. boundValue ip_reg
  ipAddr <- valueAsSegmentOff (pctxMemory ctx) ipVal
  targets <- lookup ipAddr (pctxExtResolution ctx)
  let blockState = finalAbsBlockState absState finalRegs
  let nextInitJmpBounds = Jmp.postJumpBounds jmpBounds finalRegs
  return [ (tgt, blockState, nextInitJmpBounds) | tgt <- targets ]

-- | This is a good default set of block classifiers
--
-- Block classifiers determine how the code discovery engine interprets the
-- final instruction in each block. The individual classifiers are also exported
-- so that architecture backends (or even end users) can provide their own
-- classifiers.
--
-- See 'Data.Macaw.Discovery.Classifier' for the primitives necessary to define
-- new classifiers (e.g., classifiers that can produce architecture-specific
-- terminators).
--
-- Note that classifiers are an instance of 'Control.Monad.Alternative', so the
-- order they are applied in matters.  While several are non-overlapping, at
-- least the order that the direct jump and tail call classifiers are applied in
-- matters, as they look substantially the same to the analysis. Being too eager
-- to flag jumps as tail calls classifies the jump targets as known function
-- entry points, which can interfere with other classifiers later in the
-- function.
defaultClassifier :: BlockClassifier arch ids
defaultClassifier = branchClassifier
                <|> noreturnCallClassifier
                <|> callClassifier
                <|> returnClassifier
                <|> jumpTableClassifier
                <|> pltStubClassifier
                <|> directJumpClassifier
                <|> tailCallClassifier

-- | This parses a block that ended with a fetch and execute instruction.
parseFetchAndExecute :: forall arch ids
                     .  (RegisterInfo (ArchReg arch))
                     => ArchitectureInfo arch
                     -> BlockClassifierContext arch ids
                     -> [Stmt arch ids]
                     -> ParsedContents arch ids
parseFetchAndExecute ainfo classCtx stmts = do
  case runBlockClassifier (archClassifier ainfo) classCtx of
    ClassifySucceeded _ m -> m
    ClassifyFailed rsns ->
      ParsedContents { parsedNonterm = stmts
                     , parsedTerm  = ClassifyFailure (classifierFinalRegState classCtx) rsns
                     , writtenCodeAddrs = classifierWrittenAddrs classCtx
                     , intraJumpTargets = fromMaybe [] (useExternalTargets classCtx)
                     , newFunctionAddrs = []
                     }

-- | this evalutes the statements in a block to expand the information known
-- about control flow targets of this block.
parseBlock :: ParseContext arch ids
              -- ^ Context for parsing blocks.
           -> RegState (ArchReg arch) (Value arch ids)
           -- ^ Initial register values
           -> Block arch ids
              -- ^ Block to parse
           -> Int
              -- ^ Size of block
           -> AbsBlockState (ArchReg arch)
              -- ^ Abstract state at start of block
           -> Jmp.InitJumpBounds arch
           -> ParsedContents arch ids
parseBlock ctx initRegs b sz absBlockState blockBnds = do
  let ainfo = pctxArchInfo ctx
  let mem   = pctxMemory ctx
  withArchConstraints (pctxArchInfo ctx) $ do
   let (absState, writtenAddrs) =
         let initAbsState = initAbsProcessorState mem absBlockState
          in recordWriteStmts ainfo mem initAbsState [] (blockStmts b)
   let jmpBounds = Jmp.blockEndBounds blockBnds (blockStmts b)
   case blockTerm b of
    FetchAndExecute finalRegs -> do
      -- Try to figure out what control flow statement we have.
      let classCtx = BlockClassifierContext
            { classifierParseContext = ctx
            , classifierInitRegState = initRegs
            , classifierStmts = Seq.fromList (blockStmts b)
            , classifierBlockSize = sz
            , classifierAbsState = absState
            , classifierJumpBounds = jmpBounds
            , classifierWrittenAddrs = writtenAddrs
            , classifierFinalRegState = finalRegs
            }
      parseFetchAndExecute ainfo classCtx (blockStmts b)

    -- Do nothing when this block ends in a translation error.
    TranslateError _ msg ->
      ParsedContents { parsedNonterm = blockStmts b
                     , parsedTerm = ParsedTranslateError msg
                     , writtenCodeAddrs = writtenAddrs
                     , intraJumpTargets = []
                     , newFunctionAddrs = []
                     }
    ArchTermStmt tstmt regs ->
      let r = postArchTermStmtAbsState ainfo mem absState jmpBounds regs tstmt
       in ParsedContents { parsedNonterm = blockStmts b
                         , parsedTerm  = ParsedArchTermStmt tstmt regs ((\(a,_,_) -> a) <$> r)
                         , writtenCodeAddrs = writtenAddrs
                         , intraJumpTargets = maybeToList r
                         , newFunctionAddrs = []
                         }

type CandidateFunctionMap arch
   = Map (ArchSegmentOff arch) (FunctionExploreReason (ArchAddrWidth arch))

-- | This evaluates the statements in a block to expand the
-- information known about control flow targets of this block.
addBlock :: forall s arch ids
         .  ArchConstraints arch
         => DiscoveryState arch
         -> ArchSegmentOff arch
            -- ^ Address of the block to add.
         -> FoundAddr arch
            -- ^ State leading to explore block
         -> ArchBlockPrecond arch
            -- ^ State information needed to disassemble block at this address.
         -> FunState arch s ids
         -> STL.ST s (FunState arch s ids)
addBlock ctx src finfo pr s0 = do
  let ainfo = archInfo ctx
  let mem = memory ctx
  let fnPred = ctx^.exploreFnPred
  let knownFnEntries = ctx^.trustedFunctionEntryPoints

  let initRegs = initialBlockRegs ainfo src pr
  let nonceGen = funNonceGen s0
  let prevBlockMap = s0^.curFunBlocks
  let maxSize :: Int
      maxSize =
        case Map.lookupGT src prevBlockMap of
          Just (next,_) | Just o <- diffSegmentOff next src -> fromInteger o
          _ -> fromInteger (segoffBytesLeft src)
  (b0, sz) <- STL.strictToLazyST $ disassembleFn ainfo nonceGen src initRegs maxSize
  -- Rewrite returned blocks to simplify expressions
#ifdef USE_REWRITER
  (_,b) <- do
    let archStmt = rewriteArchStmt ainfo
    let secAddrMap = memSectionIndexMap mem
    STL.strictToLazyST $ do
      rctx <- mkRewriteContext nonceGen (rewriteArchFn ainfo) archStmt pure secAddrMap
      rewriteBlock ainfo rctx b0
#else
  b <- pure b0
#endif
  let extRes = classifyFailureResolutions s0
  let funAddr = curFunAddr s0
  let pctx = ParseContext { pctxMemory         =  mem
                          , pctxArchInfo       = ainfo
                          , pctxKnownFnEntries = knownFnEntries
                          , pctxFunAddr        = funAddr
                          , pctxAddr           = src
                          , pctxExtResolution  = extRes
                          }
  let pc = parseBlock pctx initRegs b sz (foundAbstractState finfo) (foundJumpBounds finfo)
  let pb = ParsedBlock { pblockAddr    = src
                       , pblockPrecond = Right pr
                       , blockSize     = sz
                       , blockReason   = foundReason finfo
                       , blockAbstractState = foundAbstractState finfo
                       , blockJumpBounds = foundJumpBounds finfo
                       , pblockStmts     = parsedNonterm pc
                       , pblockTermStmt  = parsedTerm pc
                       }
  let pb' = dropUnusedCodeInParsedBlock ainfo pb
  flip CMS.execStateT s0 $ unFunM $ do
    id %= addFunBlock src pb'
    let insAddr :: FunctionExploreReason (ArchAddrWidth arch) -> ArchSegmentOff arch -> FunM arch s ids ()
        insAddr rsn a
          | explorableFunction mem fnPred a =
              newEntries %= Map.insertWith (\_ o -> o) a rsn
          | otherwise =
              pure ()
    mapM_ (insAddr (CallTarget src)) (newFunctionAddrs pc)
    mapM_ (insAddr (PossibleWriteEntry src)) (writtenCodeAddrs pc)
    mapM_ (mergeIntraJump ainfo src) (intraJumpTargets pc)

-- | Make an error block with no statements for the given address.
mkErrorBlock :: ArchSegmentOff arch -> FoundAddr arch -> String -> ParsedBlock arch ids
mkErrorBlock addr finfo err =
  ParsedBlock { pblockAddr = addr
              , pblockPrecond = Left err
              , blockSize = 0
              , blockReason = foundReason finfo
              , blockAbstractState = foundAbstractState finfo
              , blockJumpBounds    = foundJumpBounds finfo
              , pblockStmts = []
              , pblockTermStmt = ParsedTranslateError (Text.pack err)
              }

transfer :: ArchSegmentOff arch
         -> FunState arch s ids
         -> STL.ST s (FunState arch s ids)
transfer addr s0 = do
  let ctx = s0^.curFunCtx
  let ainfo = archInfo ctx
  withArchConstraints ainfo $ do
    let emsg = error $ "transfer called on unfound address " ++ show addr ++ "."
    let finfo = Map.findWithDefault emsg addr (s0^.foundAddrs)
    -- Get maximum number of bytes to disassemble
    case extractBlockPrecond ainfo addr (foundAbstractState finfo) of
      Left msg -> pure (addFunBlock addr (mkErrorBlock addr finfo msg) s0)
      Right pr -> addBlock ctx addr finfo pr s0

------------------------------------------------------------------------
-- Main loop

mkFunState :: PN.NonceGenerator (STS.ST s) ids
           -> DiscoveryState arch
           -> FunctionExploreReason (ArchAddrWidth arch)
              -- ^ Reason to provide for why we are analyzing this function
              --
              -- This can be used to figure out why we decided a
              -- given address identified a code location.
           -> ArchSegmentOff arch
           -> [(ArchSegmentOff arch, [ArchSegmentOff arch])]
           -> FunState arch s ids
mkFunState gen s rsn addr extraIntraTargets = do
  let faddr = FoundAddr { foundReason = FunctionEntryPoint
                        , foundAbstractState = mkInitialAbsState (archInfo s) (memory s) addr
                        , foundJumpBounds    = withArchConstraints (archInfo s) Jmp.functionStartBounds
                        }
   in FunState { funReason = rsn
               , funNonceGen = gen
               , curFunAddr  = addr
               , _curFunCtx  = s
               , _curFunBlocks = Map.empty
               , _foundAddrs = Map.singleton addr faddr
               , _reverseEdges = Map.empty
               , _frontier   = Set.fromList [ addr ]
               , _newEntries = Map.empty
               , classifyFailureResolutions = extraIntraTargets
               }

mkFunInfo :: DiscoveryState arch -> FunState arch s ids -> DiscoveryFunInfo arch ids
mkFunInfo s fs =
  let addr = curFunAddr fs
   in DiscoveryFunInfo { discoveredFunReason = funReason fs
                       , discoveredFunAddr = addr
                       , discoveredFunSymbol = Map.lookup addr (symbolNames s)
                       , _parsedBlocks = fs^.curFunBlocks
                       , discoveredClassifyFailureResolutions = classifyFailureResolutions fs
                       }

-- | Loop that repeatedly explore blocks until we have explored blocks
-- on the frontier.

reportAnalyzeBlock :: DiscoveryOptions
                      -- ^ Options controlling discovery
                   -> ArchSegmentOff arch -- ^ Function address
                   -> ArchSegmentOff arch -- ^ Block address
                   -> Maybe (BlockExploreReason (ArchAddrWidth arch))
                   -> IncComp (DiscoveryEvent arch) a
                   -> IncComp (DiscoveryEvent arch) a
reportAnalyzeBlock disOpts faddr baddr mReason
  | logAtAnalyzeBlock disOpts = IncCompLog (ReportAnalyzeBlock faddr baddr mReason)
  | otherwise = id

analyzeBlocks :: DiscoveryOptions
                -- ^ Options controlling discovery
              -> DiscoveryState arch
              -> ArchSegmentOff arch
                    -- ^ The address to explore
              -> FunState arch s ids
              -> STL.ST s (IncComp (DiscoveryEvent arch)
                                   (DiscoveryState arch, Some (DiscoveryFunInfo arch)))
analyzeBlocks disOpts ds0 faddr fs =
  case Set.minView (fs^.frontier) of
    Nothing -> do
      let finfo = mkFunInfo ds0 fs
      let ds1 = ds0
              & funInfo             %~ Map.insert faddr (Some finfo)
              & unexploredFunctions %~ Map.delete faddr
          go ds [] = IncCompDone (ds, Some finfo)
          go ds ((tgt,rsn):r)
            | shouldExploreFunction tgt ds =
              IncCompLog
                (ReportIdentifyFunction faddr tgt rsn)
                (go (ds & unexploredFunctions %~ Map.insert tgt rsn) r)
            | otherwise = go ds r
      pure $ go ds1 (Map.toList (fs^.newEntries))
    Just (baddr, next_roots) ->
      let mReason = fs^.foundAddrs.at baddr^?_Just.foundReasonL in
      fmap (reportAnalyzeBlock disOpts faddr baddr mReason) $ do
        fs' <- transfer baddr (fs & frontier .~ next_roots)
        analyzeBlocks disOpts ds0 faddr fs'

-- | Run tfunction discovery to explore blocks.
discoverFunction :: DiscoveryOptions
                -- ^ Options controlling discovery
                -> ArchSegmentOff arch
                   -- ^ The address to explore
                -> FunctionExploreReason (ArchAddrWidth arch)
                    -- ^ Reason to provide for why we are analyzing this function
                    --
                    -- This can be used to figure out why we decided a
                    -- given address identified a code location.
                -> DiscoveryState arch
                   -- ^ The current binary information.
                -> [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                   -- ^ Additional identified intraprocedural jump targets
                   --
                   -- The pairs are: (address of the block jumped from, jump targets)
                -> IncComp (DiscoveryEvent arch)
                           (DiscoveryState arch, Some (DiscoveryFunInfo arch))
discoverFunction disOpts addr rsn s extraIntraTargets = STL.runST $ do
  Some gen <- STL.strictToLazyST PN.newSTNonceGenerator
  let fs0 = mkFunState gen s rsn addr extraIntraTargets
  analyzeBlocks disOpts s addr fs0

-- | This analyzes the function at a given address, possibly
-- discovering new candidates.
--
-- This returns the updated state and the discovered control flow
-- graph for this function.
analyzeFunction :: ArchSegmentOff arch
                   -- ^ The address to explore
                -> FunctionExploreReason (ArchAddrWidth arch)
                -- ^ Reason to provide for why we are analyzing this function
                --
                -- This can be used to figure out why we decided a
                -- given address identified a code location.
                -> DiscoveryState arch
                -- ^ The current binary information.
                -> (DiscoveryState arch, Some (DiscoveryFunInfo arch))
analyzeFunction addr rsn s =
  case Map.lookup addr (s^.funInfo) of
    Just finfo -> (s, finfo)
    Nothing -> incCompResult (discoverFunction defaultDiscoveryOptions addr rsn s [])

-- | Analyze addresses that we have marked as functions, but not yet analyzed to
-- identify basic blocks, and discover new function candidates until we have
-- analyzed all function entry points.
--
-- If an exploreFnPred function exists in the DiscoveryState, then do not
-- analyze unexploredFunctions at addresses that do not satisfy this predicate.
analyzeDiscoveredFunctions :: DiscoveryState arch -> DiscoveryState arch
analyzeDiscoveredFunctions info =
  case Map.lookupMin (info^.unexploredFunctions) of
    Nothing -> info
    Just (addr, rsn) ->
      analyzeDiscoveredFunctions $! fst (analyzeFunction addr rsn info)

-- | Extend the analysis of a previously analyzed function with new
-- information about the transfers for a block in that function.  The
-- assumption is that the block in question previously had an unknown
-- transfer state condition, and that the new transfer addresses were
-- discovered by other means (e.g. SMT analysis).  The block in
-- question's terminal statement will be replaced by an ITE (from IP
-- -> new addresses) and the new addresses will be added to the
-- frontier for additional discovery.
addDiscoveredFunctionBlockTargets :: DiscoveryState arch
                                  -> DiscoveryFunInfo arch ids
                                  -- ^ The function for which we have learned additional information
                                  -> [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                                  -> DiscoveryState arch
addDiscoveredFunctionBlockTargets initState origFunInfo resolvedTargets =
  let rsn = discoveredFunReason origFunInfo
      funAddr = discoveredFunAddr origFunInfo
  in fst $ incCompResult $ discoverFunction defaultDiscoveryOptions funAddr rsn initState resolvedTargets

exploreMemPointers :: [(ArchSegmentOff arch, ArchSegmentOff arch)]
                   -- ^ List of addresses and value pairs to use for
                   -- considering possible addresses.
                   -> DiscoveryState arch
                   -> DiscoveryState arch
exploreMemPointers memWords info =
  flip CMS.execState info $ do
    F.forM_ memWords $ \(src, val) -> do
      s <- CMS.get
      let addFun = segmentFlags (segoffSegment src) `Perm.hasPerm` Perm.write
                && shouldExploreFunction val s
      when addFun $ do
        CMS.put $ markAddrAsFunction (CodePointerInMem src) val s

-- | Expand an initial discovery state by exploring from a given set of function
-- entry points.
cfgFromAddrsAndState :: forall arch
                     .  DiscoveryState arch
                     -> [ArchSegmentOff arch]
                     -- ^ Initial function entry points.
                     -> [(ArchSegmentOff arch, ArchSegmentOff arch)]
                     -- ^ Function entry points in memory to be explored
                     -- after exploring function entry points.
                     --
                     -- Each entry contains an address and the value stored in it.
                     -> DiscoveryState arch
cfgFromAddrsAndState initial_state init_addrs mem_words =
  initial_state
    & markAddrsAsFunction InitAddr init_addrs
    & analyzeDiscoveredFunctions
    & exploreMemPointers mem_words
    & analyzeDiscoveredFunctions

-- | Construct an empty discovery state and populate it by exploring from a
-- given set of function entry points
cfgFromAddrs ::
     forall arch
  .  ArchitectureInfo arch
     -- ^ Architecture-specific information needed for doing control-flow exploration.
  -> Memory (ArchAddrWidth arch)
     -- ^ Memory to use when decoding instructions.
  -> AddrSymMap (ArchAddrWidth arch)
     -- ^ Map from addresses to the associated symbol name.
  -> [ArchSegmentOff arch]
     -- ^ Initial function entry points.
     -> [(ArchSegmentOff arch, ArchSegmentOff arch)]
     -- ^ Function entry points in memory to be explored
     -- after exploring function entry points.
     --
     -- Each entry contains an address and the value stored in it.
  -> DiscoveryState arch
cfgFromAddrs ainfo mem addrSymMap =
  cfgFromAddrsAndState (emptyDiscoveryState mem addrSymMap ainfo)

------------------------------------------------------------------------
-- DiscoveryOptions

-- | Options controlling 'completeDiscoveryState'.
data DiscoveryOptions
   = DiscoveryOptions { exploreFunctionSymbols :: !Bool
                        -- ^ If @True@, 'completeDiscoveryState'
                        -- should automatically explore all addresses
                        -- in the address-to-symbol map.
                      , exploreCodeAddrInMem :: !Bool
                        -- ^ If @True@, 'completeDiscoveryState' will
                        -- explore all potential code addresses in
                        -- memory after exploring other potential
                        -- functions.
                        --
                        -- This is effectively a hack that sometimes
                        -- allows discovering functions.  If you need
                        -- it, let the author's of Macaw know so that
                        -- we can find a more principled way.
                      , logAtAnalyzeFunction  :: !Bool
                        -- ^ Print a message each time we apply
                        -- discovery analysis to a new function.
                      , logAtAnalyzeBlock     :: !Bool
                        -- ^ Print a message each time we analyze a
                        -- block within a function.
                      }

-- | Some default options
defaultDiscoveryOptions :: DiscoveryOptions
defaultDiscoveryOptions =
  DiscoveryOptions { exploreFunctionSymbols = True
                   , exploreCodeAddrInMem   = False
                   , logAtAnalyzeFunction   = True
                   , logAtAnalyzeBlock      = False
                   }

------------------------------------------------------------------------
-- Resolve functions with logging

-- | Events reported by discovery process.
data DiscoveryEvent arch
     -- | Report that discovery has now started analyzing the function at the given offset.
   = ReportAnalyzeFunction !(ArchSegmentOff arch)
     -- | @ReoptAnalyzeFunctionDone f@ we completed discovery and yielded function @f@.
   | forall ids . ReportAnalyzeFunctionDone (DiscoveryFunInfo arch ids)
     -- | @ReportIdentifyFunction src tgt rsn@ indicates Macaw identified a
     -- candidate funciton entry point @tgt@ from analyzing @src@ for the
     -- given reason @rsn@.
   | ReportIdentifyFunction
        !(ArchSegmentOff arch)
        !(ArchSegmentOff arch)
        !(FunctionExploreReason (ArchAddrWidth arch))
      -- | @ReportAnalyzeBlock faddr baddr reason@ indicates discovery
      -- identified a block at @baddr@ in @faddr@.  @reason@ is the reason why
      -- this block is explored (or sometimes re-explored).
      --
      -- N.B. This event is only emitted when `logAtAnalyzeBlock` is true.
   | ReportAnalyzeBlock
      !(ArchSegmentOff arch)
      !(ArchSegmentOff arch)
      !(Maybe (BlockExploreReason (ArchAddrWidth arch)))

ppSymbol :: MemWidth w => Maybe BSC.ByteString -> MemSegmentOff w -> String
ppSymbol (Just fnName) addr = show addr ++ " (" ++ BSC.unpack fnName ++ ")"
ppSymbol Nothing addr = show addr

logDiscoveryEvent :: MemWidth (ArchAddrWidth arch)
                  => AddrSymMap (ArchAddrWidth arch)
                  -> DiscoveryEvent arch
                  -> IO ()
logDiscoveryEvent symMap p =
  case p of
    ReportAnalyzeFunction addr -> do
      IO.hPutStrLn IO.stderr $ "Analyzing function: " ++ ppSymbol (Map.lookup addr symMap) addr
      IO.hFlush IO.stderr
    ReportAnalyzeFunctionDone _ -> do
      pure ()
    ReportIdentifyFunction _ tgt rsn -> do
      IO.hPutStrLn IO.stderr $ "  Identified candidate entry point "
                       ++ ppSymbol (Map.lookup tgt symMap) tgt
                       ++ " " ++ ppFunReason rsn
      IO.hFlush IO.stderr
    ReportAnalyzeBlock _ baddr _ -> do
      IO.hPutStrLn IO.stderr $ "  Analyzing block: " ++ show baddr
      IO.hFlush IO.stderr

resolveFuns :: DiscoveryOptions
               -- ^ Options controlling discovery
            -> DiscoveryState arch
            -> IncCompM (DiscoveryEvent arch) r (DiscoveryState arch)
resolveFuns disOpts info = seq info $ withArchConstraints (archInfo info) $ do
  case Map.minViewWithKey (info^.unexploredFunctions) of
    Nothing -> pure info
    Just ((addr, rsn), _) -> do
      when (logAtAnalyzeFunction disOpts) $ do
        incCompLog (ReportAnalyzeFunction addr)
      if Map.member addr (info^.funInfo) then
        resolveFuns disOpts info
       else do
        (info', Some f) <- liftIncComp id $ discoverFunction disOpts addr rsn info []
        incCompLog $ ReportAnalyzeFunctionDone f
        resolveFuns disOpts info'

------------------------------------------------------------------------
-- Top-level discovery

-- | Explore until we have found all functions we can.
--
-- This function is a version of completeDiscoveryState that uses the
-- new incremental computation monad rather than IO.
incCompleteDiscovery :: forall arch r
                     .  DiscoveryState arch
                     -> DiscoveryOptions
                        -- ^ Options controlling discovery
                     -> IncCompM (DiscoveryEvent arch) r (DiscoveryState arch)
incCompleteDiscovery initState disOpt = do
 let ainfo = archInfo initState
 let mem = memory initState
 let symMap = symbolNames initState
 withArchConstraints ainfo $ do
  -- Add symbol table entries to discovery state if requested
  let postSymState
        | exploreFunctionSymbols disOpt =
            initState & markAddrsAsFunction InitAddr (Map.keys symMap)
        | otherwise = initState
  -- Discover functions
  postPhase1Discovery <- resolveFuns disOpt postSymState
  -- Discovery functions from memory
  if exploreCodeAddrInMem disOpt then do
    -- Execute hack of just searching for pointers in memory.
    let memContents = withArchConstraints ainfo $ memAsAddrPairs mem LittleEndian
    resolveFuns disOpt $ postPhase1Discovery & exploreMemPointers memContents
   else
    return postPhase1Discovery

-- | Explore until we have found all functions we can.
--
-- This function is intended to make it easy to explore functions, and
-- can be controlled via 'DiscoveryOptions'.
completeDiscoveryState :: forall arch
                       .  DiscoveryState arch
                       -> DiscoveryOptions
                          -- ^ Options controlling discovery
                       -> IO (DiscoveryState arch)
completeDiscoveryState initState disOpt = do
  let ainfo = archInfo initState
  let symMap = symbolNames initState
  withArchConstraints ainfo $
    processIncCompLogs (logDiscoveryEvent symMap) $ runIncCompM $
      incCompleteDiscovery initState disOpt
