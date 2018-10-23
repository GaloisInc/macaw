{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.SemMC.Generator (
  -- * Expressions
  Expr(..),
  -- * Blocks
  BlockSeq(..),
  nextBlockID,
  frontierBlocks,
  PreBlock(..),
  pBlockStmts,
  pBlockState,
  GenState(..),
  initGenState,
  initRegState,
  blockSeq,
  blockState,
  finishBlock,
  finishBlock',
  -- * State updates
  curRegState,
  setRegVal,
  addStmt,
  addAssignment,
  addExpr,
  finishWithTerminator,
  conditionalBranch,
  asAtomicStateUpdate,
  -- * State access
  getRegs,
  getRegValue,
  -- * Results
  GenResult(..),
  -- * Monad
  GenCont,
  Generator,
  runGenerator,
  shiftGen,
  genResult,
  -- * Errors
  GeneratorError(..)
  ) where

import           GHC.TypeLits

import           Control.Lens
import qualified Control.Monad.Cont as Ct
import qualified Control.Monad.Except as ET
import qualified Control.Monad.Reader as Rd
import           Control.Monad.ST ( ST )
import qualified Control.Monad.State.Strict as St
import           Control.Monad.Trans ( lift )
import qualified Data.Foldable as F
import           Data.Maybe ( fromMaybe )
import qualified Data.Sequence as Seq
import           Data.Word (Word64)

import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types ( BoolType )
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as NC

import           Data.Macaw.SemMC.Simplify ( simplifyValue, simplifyApp )

data Expr arch ids tp where
  ValueExpr :: !(Value arch ids tp) -> Expr arch ids tp
  AppExpr   :: !(App (Value arch ids) tp) -> Expr arch ids tp

data GenResult arch ids =
  GenResult { resBlockSeq :: BlockSeq arch ids
            , resState :: Maybe (PreBlock arch ids)
            }

data BlockSeq arch ids =
  BlockSeq { _nextBlockID :: !Word64
           , _frontierBlocks :: !(Seq.Seq (Block arch ids))
           }

deriving instance Show (Block arch ids) => Show (BlockSeq arch ids)
-- deriving instance (PPCArchConstraints ppc) => Show (Block ppc ids)
-- deriving instance (PPCArchConstraints ppc) => Show (TermStmt ppc ids)

-- | Control flow blocs generated so far.
nextBlockID :: Simple Lens (BlockSeq arch ids) Word64
nextBlockID = lens _nextBlockID (\s v -> s { _nextBlockID = v })

-- | Blocks that are not in CFG that end with a FetchAndExecute,
-- which we need to analyze to compute new potential branch targets.
frontierBlocks :: Simple Lens (BlockSeq arch ids) (Seq.Seq (Block arch ids))
frontierBlocks = lens _frontierBlocks (\s v -> s { _frontierBlocks = v })

data PreBlock arch ids =
  PreBlock { pBlockIndex :: !Word64
           , pBlockAddr :: MM.MemSegmentOff (ArchAddrWidth arch)
           , _pBlockStmts :: !(Seq.Seq (Stmt arch ids))
           , _pBlockState :: !(RegState (ArchReg arch) (Value arch ids))
           }

-- | An accessor for the current statements in the 'PreBlock'
pBlockStmts :: Simple Lens (PreBlock arch ids) (Seq.Seq (Stmt arch ids))
pBlockStmts = lens _pBlockStmts (\s v -> s { _pBlockStmts = v })

-- | An accessor for the current register state held in the 'PreBlock'
pBlockState :: Simple Lens (PreBlock arch ids) (RegState (ArchReg arch) (Value arch ids))
pBlockState = lens _pBlockState (\s v -> s { _pBlockState = v })

data GenState arch ids s =
  GenState { assignIdGen :: NC.NonceGenerator (ST s) ids
           , _blockSeq :: !(BlockSeq arch ids)
           , _blockState :: !(PreBlock arch ids)
           , genAddr :: MM.MemSegmentOff (ArchAddrWidth arch)
           , genRegUpdates :: MapF.MapF (ArchReg arch) (Value arch ids)
           }

emptyPreBlock :: RegState (ArchReg arch) (Value arch ids)
              -> Word64
              -> MM.MemSegmentOff (RegAddrWidth (ArchReg arch))
              -> PreBlock arch ids
emptyPreBlock s0 idx addr =
  PreBlock { pBlockIndex = idx
           , pBlockAddr = addr
           , _pBlockStmts = Seq.empty
           , _pBlockState = s0
           }

initGenState :: NC.NonceGenerator (ST s) ids
             -> MM.MemSegmentOff (ArchAddrWidth arch)
             -> RegState (ArchReg arch) (Value arch ids)
             -> GenState arch ids s
initGenState nonceGen addr st =
  GenState { assignIdGen = nonceGen
           , _blockSeq = BlockSeq { _nextBlockID = 1, _frontierBlocks = Seq.empty }
           , _blockState = emptyPreBlock st 0 addr
           , genAddr = addr
           , genRegUpdates = MapF.empty
           }

initRegState :: (KnownNat (RegAddrWidth (ArchReg arch)),
                 1 <= RegAddrWidth (ArchReg arch),
                 RegisterInfo (ArchReg arch),
                 MM.MemWidth (RegAddrWidth (ArchReg arch)))
             => MM.MemSegmentOff (RegAddrWidth (ArchReg arch))
             -> RegState (ArchReg arch) (Value arch ids)
initRegState startIP =
  mkRegState Initial & curIP .~ RelocatableValue (addrWidthRepr startIP) (MM.segoffAddr startIP)

blockSeq :: Simple Lens (GenState arch ids s) (BlockSeq arch ids)
blockSeq = lens _blockSeq (\s v -> s { _blockSeq = v })

blockState :: Simple Lens (GenState arch ids s) (PreBlock arch ids)
blockState = lens _blockState (\s v -> s { _blockState = v })

curRegState :: Simple Lens (GenState arch ids s) (RegState (ArchReg arch) (Value arch ids))
curRegState = blockState . pBlockState

-- | This combinator collects state modifications by a single instruction into a single 'ArchState' statement
--
-- This function is meant to be wrapped around an atomic CPU state
-- transformation.  It collects all of the updates to the CPU register state
-- (which are assumed to be made through the 'setRegVal' function) and coalesces
-- them into a new macaw 'ArchState' statement that records the updates for
-- later analysis.
--
-- The state is hidden in the generator monad and collected after the
-- transformer is executed.  Note: if the transformer splits the state, it isn't
-- obvious what will happen here.  The mechanism is not designed with that use
-- case in mind.
asAtomicStateUpdate :: ArchMemAddr arch
                    -- ^ Instruction address
                    -> Generator arch ids s a
                    -- ^ An action recording the state transformations of the instruction
                    -> Generator arch ids s a
asAtomicStateUpdate insnAddr transformer = do
  St.modify $ \s -> s { genRegUpdates = MapF.empty }
  res <- transformer
  updates <- St.gets genRegUpdates
  addStmt (ArchState insnAddr updates)
  return res

-- | Update the value of a machine register (in the 'Generator' state) with a
-- new macaw 'Value'.  This function applies a simplifier ('simplifyValue') to
-- the value first, if possible.
setRegVal :: (OrdF (ArchReg arch), MM.MemWidth (RegAddrWidth (ArchReg arch)))
          => ArchReg arch tp
          -> Value arch ids tp
          -> Generator arch ids s ()
setRegVal reg val = do
  St.modify $ \s -> s { genRegUpdates = MapF.insert reg val (genRegUpdates s) }
  curRegState . boundValue reg .= fromMaybe val (simplifyValue val)

addExpr :: (OrdF (ArchReg arch), MM.MemWidth (RegAddrWidth (ArchReg arch)))
        => Expr arch ids tp
        -> Generator arch ids s (Value arch ids tp)
addExpr expr =
  case expr of
    ValueExpr val -> return val
    AppExpr app
      | Just val <- simplifyApp app -> return val
      | otherwise -> AssignedValue <$> addAssignment (EvalApp app)

data GeneratorError = InvalidEncoding
                    | GeneratorMessage String
  deriving (Show)

-- | This is a state monad (with error termination via 'ET.ExceptT') built on
-- top of 'Ct.ContT' and 'Rd.ReaderT'.
--
-- We use the 'Ct.ContT' for early termination when dealing with control flow
-- terminators (e.g., syscall) and to split for dealing with conditional
-- branches.
--
-- The state is managed by explicitly passing it through the continuation.
--
-- The most important operation provided is the primitive 'shiftGen', which is
-- used to build 'conditionalBranch'.
--
-- The base monad is 'ST', which is used for nonce generation.
newtype Generator arch ids s a =
  Generator { runG :: Ct.ContT (GenResult arch ids)
                               (Rd.ReaderT (GenState arch ids s)
                                           (ET.ExceptT GeneratorError (ST s))) a }
                               deriving (Applicative,
                                         Functor,
                                         Rd.MonadReader (GenState arch ids s),
                                         Ct.MonadCont)
-- | The 'Monad' instance is manually-specified so that calls to 'fail' actually
-- use our 'ET.ExceptT' 'ET.throwError' for nicer error behavior.
instance Monad (Generator arch ids s) where
  return v = Generator (return v)
  Generator m >>= h = Generator (m >>= \v -> runG (h v))
  Generator m >> Generator n = Generator (m >> n)
  fail msg = Generator (Ct.ContT (\_ -> ET.throwError (GeneratorMessage msg)))

instance St.MonadState (GenState arch ids s) (Generator arch ids s) where
  get = Generator Rd.ask
  put nextState = Generator $ Ct.ContT $ \c -> Rd.ReaderT $ \_s ->
    Rd.runReaderT (c ()) nextState

instance ET.MonadError GeneratorError (Generator arch ids s) where
  throwError e = Generator (Ct.ContT (\_ -> ET.throwError e))

-- | The type of continuations provided by 'shiftGen'
type GenCont arch ids s a = a -> GenState arch ids s -> ET.ExceptT GeneratorError (ST s) (GenResult arch ids)

-- | Given a final continuation to call, run the generator (and produce a final
-- result with the given continuation @k@).  Also takes an initial state.
runGenerator :: GenCont arch ids s a
             -> GenState arch ids s
             -> Generator arch ids s a
             -> ET.ExceptT GeneratorError (ST s) (GenResult arch ids)
runGenerator k st (Generator m) = Rd.runReaderT (Ct.runContT m (Rd.ReaderT . k)) st

-- | Capture the current continuation and execute an action that gets that
-- continuation as an argument (it can be invoked as many times as desired).
shiftGen :: (GenCont arch ids s a -> GenState arch ids s -> ET.ExceptT GeneratorError (ST s) (GenResult arch ids))
         -> Generator arch ids s a
shiftGen f =
  Generator $ Ct.ContT $ \k -> Rd.ReaderT $ \s -> f (Rd.runReaderT . k) s

genResult :: (Monad m) => a -> GenState arch ids s -> m (GenResult arch ids)
genResult _ s = do
  return GenResult { resBlockSeq = s ^. blockSeq
                   , resState = Just (s ^. blockState)
                   }

-- | Append a statement (on the right) to the list of statements in the current
-- 'PreBlock'.
addStmt :: Stmt arch ids -> Generator arch ids s ()
addStmt stmt = (blockState . pBlockStmts) %= (Seq.|> stmt)

-- | Generate the next unique ID for an assignment using the nonce generator
newAssignId :: Generator arch ids s (AssignId ids tp)
newAssignId = do
  nonceGen <- St.gets assignIdGen
  AssignId <$> liftST (NC.freshNonce nonceGen)

-- | Lift an 'ST' action into 'PPCGenerator'
liftST :: ST s a -> Generator arch ids s a
liftST = Generator . lift . lift . lift

-- | Append an assignment statement to the list of statements in the current
-- 'PreBlock'
addAssignment :: AssignRhs arch (Value arch ids) tp
              -> Generator arch ids s (Assignment arch ids tp)
addAssignment rhs = do
  l <- newAssignId
  let a = Assignment l rhs
  addStmt (AssignStmt a)
  return a

-- | Get all of the current register values
--
-- This is meant to be used to snapshot the register state at the beginning of
-- an instruction transformer so that we can perform atomic updates to the
-- machine state (by reading values from the captured initial state).
getRegs :: Generator arch ids s (RegState (ArchReg arch) (Value arch ids))
getRegs = do
  genState <- St.get
  return (genState ^. (blockState . pBlockState))

-- | Get the value of a single register.
--
-- NOTE: This should not be called from the generated semantics transformers.
-- Those must get their register values through 'getRegs', which is used to take
-- a snapshot of the register state at the beginning of each instruction.  This
-- is required for instruction updates to register values to have the necessary
-- atomic update behavior.
getRegValue :: (OrdF (ArchReg arch)) => ArchReg arch tp -> Generator arch ids s (Value arch ids tp)
getRegValue r = do
  genState <- St.get
  return (genState ^. (blockState . pBlockState . boundValue r))

-- | Finish a block immediately with the given terminator statement
--
-- This uses the underlying continuation monad to skip the normal
-- post-instruction behavior.
--
-- NOTE: We do not do an explicit instruction pointer update; the handler for
-- architecture-specific terminator statements handles that.
finishWithTerminator :: (RegState (ArchReg arch) (Value arch ids) -> TermStmt arch ids)
                     -> Generator arch ids s a
finishWithTerminator term =
  shiftGen $ \_ s0 -> do
  let pre_block = s0 ^. blockState
  let fin_block = finishBlock' pre_block term
  return GenResult { resBlockSeq = s0 ^. blockSeq & frontierBlocks %~ (Seq.|> fin_block)
                   , resState = Nothing
                   }

-- | Convert the contents of a 'PreBlock' (a block being constructed) into a
-- full-fledged 'Block'
--
-- The @term@ function is used to create the terminator statement of the block.
finishBlock' :: PreBlock arch ids
             -> (RegState (ArchReg arch) (Value arch ids) -> TermStmt arch ids)
             -> Block arch ids
finishBlock' preBlock term =
  Block { blockLabel = pBlockIndex preBlock
        , blockStmts = F.toList (preBlock ^. pBlockStmts)
        , blockTerm = term (preBlock ^. pBlockState)
        }

-- | Consume a 'GenResult', finish off the contained 'PreBlock', and append the
-- new block to the block frontier.
finishBlock :: (RegState (ArchReg arch) (Value arch ids) -> TermStmt arch ids)
            -> GenResult arch ids
            -> BlockSeq arch ids
finishBlock term st =
  case resState st of
    Nothing -> resBlockSeq st
    Just preBlock ->
      let b = finishBlock' preBlock term
      in resBlockSeq st & frontierBlocks %~ (Seq.|> b)

-- | A primitive for splitting execution in the presence of conditional
-- branches.
--
-- This function uses the underlying continuation monad to split execution.  It
-- captures the current continuation and builds a block for the true branch and
-- another block for the false branch.  It manually threads the state between
-- the two branches and makes updates to keep them consistent.  It also joins
-- the two exploration frontiers after processing the true and false branches so
-- that the underlying return value contains all discovered blocks.
conditionalBranch :: (OrdF (ArchReg arch),
                      MM.MemWidth (RegAddrWidth (ArchReg arch)))
                  => Value arch ids BoolType
                  -- ^ The conditional guarding the branch
                  -> Generator arch ids s ()
                  -- ^ The action to take on the true branch
                  -> Generator arch ids s ()
                  -- ^ The action to take on the false branch
                  -> Generator arch ids s ()
conditionalBranch condExpr t f =
  go (fromMaybe condExpr (simplifyValue condExpr))
  where
    go condv =
      case condv of
        BoolValue True -> t
        BoolValue False -> f
        _ -> shiftGen $ \c s0 -> do
          let pre_block = s0 ^. blockState
          let st = pre_block ^. pBlockState
          let t_block_label = s0 ^. blockSeq ^. nextBlockID
          let s1 = s0 & blockSeq . nextBlockID +~ 1
                      & blockSeq . frontierBlocks .~ Seq.empty
                      & blockState .~ emptyPreBlock st t_block_label (genAddr s0)

          -- Explore the true block
          t_seq <- finishBlock FetchAndExecute <$> runGenerator c s1 t

          -- Explore the false block
          let f_block_label = t_seq ^. nextBlockID
          let s2 = GenState { assignIdGen = assignIdGen s0
                            , _blockSeq = BlockSeq { _nextBlockID = t_seq ^. nextBlockID + 1
                                                   , _frontierBlocks = Seq.empty
                                                   }
                            , _blockState = emptyPreBlock st f_block_label (genAddr s0)
                            , genAddr = genAddr s0
                            , genRegUpdates = genRegUpdates s0
                            }
          f_seq <- finishBlock FetchAndExecute <$> runGenerator c s2 f

          -- Join the results with a branch terminator
          let fin_block = finishBlock' pre_block (\_ -> Branch condv t_block_label f_block_label)
          let frontier = mconcat [ s0 ^. blockSeq ^. frontierBlocks Seq.|> fin_block
                                 , t_seq ^. frontierBlocks
                                 , f_seq ^. frontierBlocks
                                 ]
          return GenResult { resBlockSeq =
                             BlockSeq { _nextBlockID = _nextBlockID f_seq
                                      , _frontierBlocks = frontier
                                      }
                           , resState = Nothing
                           }
