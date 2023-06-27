{-|
This defines the architecture-specific information needed for code discovery.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TypeFamilies #-}
module Data.Macaw.Architecture.Info
  ( ArchitectureInfo(..)
  , postCallAbsState
  , DisassembleFn
   -- * Block classification
  , BlockClassifier
  , BlockClassifierM
  , runBlockClassifier
  , BlockClassifierContext(..)
  , Classifier(..)
  , classifierLog
  , tryClassifier
  , classifierGuard
  , classifierName
  , liftClassifier
  , ParseContext(..)
  , NoReturnFunStatus(..)
    -- * Unclassified blocks
  , module Data.Macaw.CFG.Block
  , rewriteBlock
  ) where

import           Control.Applicative ( Alternative(..), liftA )
import           Control.Monad ( ap, guard )
import qualified Control.Monad.Fail as MF
import qualified Control.Monad.Reader as CMR
import qualified Control.Monad.Trans as CMT
import           Control.Monad.ST ( ST )
import           Data.Map ( Map )
import           Data.Parameterized.Nonce
import           Data.Parameterized.TraversableF
import           Data.Sequence (Seq)

import           Data.Macaw.AbsDomain.AbsState as AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import           Data.Macaw.CFG.Block
import           Data.Macaw.CFG.Core
import           Data.Macaw.CFG.DemandSet
import           Data.Macaw.CFG.Rewriter
import qualified Data.Macaw.Discovery.ParsedContents as Parsed
import           Data.Macaw.Memory


------------------------------------------------------------------------
-- NoReturnFunStatus

-- | Flags whether a function is labeled no return or not.
data NoReturnFunStatus
   = NoReturnFun
     -- ^ Function labeled no return
   | MayReturnFun
     -- ^ Function may retun

type ClassificationError = String

-- | The result of block classification, which collects information about all of
-- the match failures to help diagnose shortcomings in the analysis
data Classifier o = ClassifyFailed    [ClassificationError]
                  | ClassifySucceeded [ClassificationError] o

-- | Log a message into the classifier's message collection. This
-- is useful when tracing information needs to be stored alongside
-- classifier errors.
classifierLog :: String -> Classifier ()
classifierLog msg = ClassifySucceeded [msg] ()

-- | Given a Classifier, build a new unconditionally succeeding one that
-- indicates whether the given classifier failed, but also carries all
-- of its errors and tracing information.
tryClassifier :: Classifier a -> Classifier Bool
tryClassifier (ClassifyFailed msgs) = ClassifySucceeded msgs False
tryClassifier (ClassifySucceeded msgs _) = ClassifySucceeded msgs True

-- | A Classifier-specific version of 'guard' that emits a log message
-- with the specified prefix if the guard expression is False (and also
-- fails).
classifierGuard :: String -> Bool -> Classifier ()
classifierGuard _ True = return ()
classifierGuard msg False = do
    classifierLog $ "guard failed for: " <> msg
    guard False

-- | In the given context, set the name of the current classifier
--
-- This is used to improve the labels for each classifier failure
classifierName :: String -> BlockClassifierM arch ids a -> BlockClassifierM arch ids a
classifierName nm (BlockClassifier (CMR.ReaderT m)) = BlockClassifier $ CMR.ReaderT $ \i ->
  case m i of
    ClassifyFailed [] -> ClassifyFailed [nm ++ " classification failed."]
    ClassifyFailed l  -> ClassifyFailed (fmap ((nm ++ ": ") ++)  l)
    ClassifySucceeded l a -> ClassifySucceeded (fmap ((nm ++ ": ") ++)  l) a

classifyFail :: Classifier a
classifyFail = ClassifyFailed []

classifySuccess :: a -> Classifier a
classifySuccess = \x -> ClassifySucceeded [] x

classifyBind :: Classifier a -> (a -> Classifier b) -> Classifier b
classifyBind m f =
  case m of
    ClassifyFailed e -> ClassifyFailed e
    ClassifySucceeded [] a -> f a
    ClassifySucceeded l a ->
      case f a of
        ClassifyFailed    e   -> ClassifyFailed    (l++e)
        ClassifySucceeded e b -> ClassifySucceeded (l++e) b

classifyAppend :: Classifier a -> Classifier a -> Classifier a
classifyAppend m n =
  case m of
    ClassifySucceeded e a -> ClassifySucceeded e a
    ClassifyFailed [] -> n
    ClassifyFailed e ->
      case n of
        ClassifySucceeded f a -> ClassifySucceeded (e++f) a
        ClassifyFailed f      -> ClassifyFailed    (e++f)

instance Alternative Classifier where
  empty = classifyFail
  (<|>) = classifyAppend

instance Functor Classifier where
  fmap = liftA

instance Applicative Classifier where
  pure = classifySuccess
  (<*>) = ap

instance Monad Classifier where
  (>>=) = classifyBind

instance MF.MonadFail Classifier where
  fail = \m -> ClassifyFailed [m]

------------------------------------------------------------------------
-- ParseContext

-- | Information needed to parse the processor state
data ParseContext arch ids =
  ParseContext { pctxMemory         :: !(Memory (ArchAddrWidth arch))
               , pctxArchInfo       :: !(ArchitectureInfo arch)
               , pctxKnownFnEntries :: !(Map (ArchSegmentOff arch) NoReturnFunStatus)
                 -- ^ Entry addresses for known functions (e.g. from
                 -- symbol information)
                 --
                 -- The discovery process will not create
                 -- intra-procedural jumps to the entry points of new
                 -- functions.
               , pctxFunAddr        :: !(ArchSegmentOff arch)
                 -- ^ Address of function containing this block.
               , pctxAddr           :: !(ArchSegmentOff arch)
                 -- ^ Address of the current block
               , pctxExtResolution :: [(ArchSegmentOff arch, [ArchSegmentOff arch])]
                 -- ^ Externally-provided resolutions for classification
                 -- failures, which are used in parseFetchAndExecute
               }

{-| The fields of the 'BlockClassifierContext' are:

  [@ParseContext ...@]: The context for the parse

  [@RegState ...@]: Initial register values

  [@Seq (Stmt ...)@]: The statements in the block

  [@AbsProcessorState ...@]: Abstract state of registers prior to
                             terminator statement being executed.

  [@Jmp.IntraJumpBounds ...@]: Bounds prior to terminator statement
                               being executed.

  [@ArchSegmentOff arch@]: Address of all segments written to memory

  [@RegState ...@]: Final register values
-}
data BlockClassifierContext arch ids = BlockClassifierContext
  { classifierParseContext  :: !(ParseContext arch ids)
  -- ^ Information needed to construct abstract processor states
  , classifierInitRegState  :: !(RegState (ArchReg arch) (Value arch ids))
  -- ^ The (concrete) register state at the beginning of the block
  , classifierStmts         :: !(Seq (Stmt arch ids))
  -- ^ The statements of the block (without the terminator)
  , classifierBlockSize     :: !Int
    -- ^ Size of block being classified.
  , classifierAbsState      :: !(AbsProcessorState (ArchReg arch) ids)
  -- ^ The abstract processor state before the terminator is executed
  , classifierJumpBounds    :: !(Jmp.IntraJumpBounds arch ids)
  -- ^ The relational abstract processor state before the terminator is executed
  , classifierWrittenAddrs  :: !([ArchSegmentOff arch])
  -- ^ The addresses of observed memory writes in the block
  , classifierFinalRegState :: !(RegState (ArchReg arch) (Value arch ids))
  -- ^ The final (concrete) register state before the terminator is executed
  }

type BlockClassifier arch ids = BlockClassifierM arch ids (Parsed.ParsedContents arch ids)

-- | The underlying monad for the 'BlockClassifier', which handles collecting
-- matching errors
newtype BlockClassifierM arch ids a =
  BlockClassifier { unBlockClassifier :: CMR.ReaderT (BlockClassifierContext arch ids)
                                                     Classifier
                                                     a
                  }
  deriving ( Functor
           , Applicative
           , Alternative
           , Monad
           , MF.MonadFail
           , CMR.MonadReader (BlockClassifierContext arch ids)
           )

-- | Run a classifier in a given block context
runBlockClassifier
  :: BlockClassifier arch ids
  -> BlockClassifierContext arch ids
  -> Classifier (Parsed.ParsedContents arch ids)
runBlockClassifier cl = CMR.runReaderT (unBlockClassifier cl)

liftClassifier :: Classifier a -> BlockClassifierM arch ids a
liftClassifier c = BlockClassifier (CMT.lift c)

------------------------------------------------------------------------
-- ArchitectureInfo

-- | Function for disassembling a range of code (usually a function in
-- the target code image) into blocks.
--
-- A block is defined as a contiguous region of code with a single known
-- entrance and potentially multiple exits.
--
-- This returns the list of blocks, the number of bytes in the blocks,
-- and any potential error that prematurely terminated translating the
-- block.
type DisassembleFn arch
   = forall s ids
   .  NonceGenerator (ST s) ids
   -> ArchSegmentOff arch
      -- ^ The offset to start reading from.
   -> RegState (ArchReg arch) (Value arch ids)
      -- ^ Initial values to use for registers.
   -> Int
      -- ^ Maximum offset for this to read from.
   -> ST s (Block arch ids, Int)

-- | This records architecture specific functions for analysis.
data ArchitectureInfo arch
   = ArchitectureInfo
     { withArchConstraints :: forall a . (ArchConstraints arch => a) -> a
       -- ^ Provides the architecture constraints to any computation
       -- that needs it.
     , archAddrWidth :: !(AddrWidthRepr (RegAddrWidth (ArchReg arch)))
       -- ^ Architecture address width.
     , archEndianness :: !Endianness
       -- ^ The byte order values are stored in.
     , extractBlockPrecond :: !(ArchSegmentOff arch
                                -> AbsBlockState (ArchReg arch)
                                -> Either String (ArchBlockPrecond arch))
       -- ^ Attempt to use abstract domain information to extract
       -- information needed to translate block.
     , initialBlockRegs :: !(forall ids
                             .  ArchSegmentOff arch
                             -> ArchBlockPrecond arch
                             -> RegState (ArchReg arch) (Value arch ids))
       -- ^ Create initial registers from address and precondition.
     , disassembleFn :: !(DisassembleFn arch)
       -- ^ Function for disassembling a block.
     , mkInitialAbsState :: !(Memory (RegAddrWidth (ArchReg arch))
                         -> ArchSegmentOff arch
                         -> AbsBlockState (ArchReg arch))
       -- ^ Creates an abstract block state for representing the beginning of a
       -- function.
       --
       -- The address is the entry point of the function.
     , absEvalArchFn :: !(forall ids tp
                          .  AbsProcessorState (ArchReg arch) ids
                          -> ArchFn arch (Value arch ids) tp
                          -> AbsValue (RegAddrWidth (ArchReg arch)) tp)
       -- ^ Evaluates an architecture-specific function
     , absEvalArchStmt :: !(forall ids
                            .  AbsProcessorState (ArchReg arch) ids
                            -> ArchStmt arch (Value arch ids)
                            -> AbsProcessorState (ArchReg arch) ids)
       -- ^ Evaluates an architecture-specific statement
     , identifyCall :: forall ids
                    .  Memory (ArchAddrWidth arch)
                    -> Seq (Stmt arch ids)
                    -> RegState (ArchReg arch) (Value arch ids)
                    -> Maybe (Seq (Stmt arch ids), ArchSegmentOff arch)
       -- ^ Function for recognizing call statements.
       --
       -- Given a memory state, list of statements, and final register
       -- state, the should determine if this is a call, and if so,
       -- return the statements with any action to push the return
       -- value to the stack removed, and provide the return address that
       -- the function should return to.
     , archCallParams :: !(CallParams (ArchReg arch))
       -- ^ Update the abstract state after a function call returns

     , checkForReturnAddr :: forall ids
                          .  RegState (ArchReg arch) (Value arch ids)
                          -> AbsProcessorState (ArchReg arch) ids
                          -> Classifier Bool
       -- ^ @checkForReturnAddr regs s@ returns true if the location
       -- where the return address is normally stored in regs when
       -- calling a function does indeed contain the abstract value
       -- associated with return addresses.
       --
       -- For x86 this checks if the address just above the stack is the
       -- return address.  For ARM, this should check the link register.
       --
       -- This predicate is invoked when considering if a potential tail call
       -- is setup to return to the right location.
     , identifyReturn :: forall ids
                      .  Seq (Stmt arch ids)
                      -> RegState (ArchReg arch) (Value arch ids)
                      -> AbsProcessorState (ArchReg arch) ids
                      -> Classifier (Seq (Stmt arch ids))
       -- ^ Identify returns to the classifier.
       --
       -- Given a list of statements and the final state of the registers, this
       -- should return 'Just stmts' if this code looks like a function return.
       -- The stmts should be a subset of the statements, but may remove unneeded memory
       -- accesses like reading the stack pointer.
     , rewriteArchFn :: (forall s src tgt tp
                         .  ArchFn arch (Value arch src) tp
                         -> Rewriter arch s src tgt (Value arch tgt tp))
       -- ^ This rewrites an architecture specific statement
     , rewriteArchStmt :: (forall s src tgt
                           .  ArchStmt arch (Value arch src)
                           -> Rewriter arch s src tgt ())
       -- ^ This rewrites an architecture specific statement
     , rewriteArchTermStmt :: (forall s src tgt . ArchTermStmt arch (Value arch src)
                                             -> Rewriter arch s src tgt (ArchTermStmt arch (Value arch tgt)))
       -- ^ This rewrites an architecture specific statement
     , archDemandContext :: !(DemandContext arch)
       -- ^ Provides architecture-specific information for computing which arguments must be
       -- evaluated when evaluating a statement.
     , postArchTermStmtAbsState :: !(forall ids
                                     .  Memory (ArchAddrWidth arch)
                                        -- The abstract state when block terminates.
                                     -> AbsProcessorState (ArchReg arch) ids
                                        -- The registers before executing terminal statement
                                     -> Jmp.IntraJumpBounds arch ids
                                     -> RegState (ArchReg arch) (Value arch ids)
                                        -- The architecture-specific statement
                                     -> ArchTermStmt arch (Value arch ids)
                                     -> Maybe (Jmp.IntraJumpTarget arch))
       -- ^ This takes an abstract state from before executing an abs
       -- state, and an architecture-specific terminal statement.
       --
       -- If the statement does not return to this function, this
       -- function should return `Nothing`.  Otherwise, it should
       -- returns the next address within the procedure that the
       -- statement jumps to along with the updated abstract state.
       --
       -- Note that per their documentation, architecture specific
       -- statements may return to at most one location within a
       -- function.
     , archClassifier :: !(forall ids . BlockClassifier arch ids)
     -- ^ The block classifier to use for this architecture, which can be
     -- customized
     }

postCallAbsState :: ArchitectureInfo arch
                 -> AbsProcessorState (ArchReg arch) ids
                 -- ^ Processor state at call.
                 -> RegState (ArchReg arch) (Value arch ids)
                 -- ^  Register values when call occurs.
                 -> ArchSegmentOff arch
                 -- ^ Return address
                 -> AbsBlockState (ArchReg arch)
postCallAbsState ainfo = withArchConstraints ainfo $
  absEvalCall (archCallParams ainfo)

-- | Apply optimizations to a terminal statement.
rewriteTermStmt :: ArchitectureInfo arch
                -> TermStmt arch src
                -> Rewriter arch s src tgt (TermStmt arch tgt)
rewriteTermStmt info tstmt = do
  case tstmt of
    FetchAndExecute regs ->
      FetchAndExecute <$> traverseF rewriteValue regs
    TranslateError regs msg ->
      TranslateError <$> traverseF rewriteValue regs
                     <*> pure msg
    ArchTermStmt ts regs ->
      ArchTermStmt <$> rewriteArchTermStmt info ts
                   <*> traverseF rewriteValue regs

-- | Apply optimizations to code in the block
rewriteBlock :: ArchitectureInfo arch
             -> RewriteContext arch s src tgt
             -> Block arch src
             -> ST s (RewriteContext arch s src tgt, Block arch tgt)
rewriteBlock info rwctx b = do
  (rwctx', tgtStmts, tgtTermStmt) <- runRewriter rwctx $ do
    mapM_ rewriteStmt (blockStmts b)
    rewriteTermStmt info (blockTerm b)
  -- Return rewritten block and any new blocks
  let rwBlock = Block { blockStmts = tgtStmts
                      , blockTerm  = tgtTermStmt
                      }
  pure (rwctx', rwBlock)
