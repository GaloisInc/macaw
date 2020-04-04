{-# LANGUAGE CPP #-}
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
  PreBlock(..),
  pBlockStmts,
  pBlockState,
  GenState(..),
  initGenState,
  initRegState,
  blockState,
  finishBlock',
  -- * State updates
  PartialBlock(..),
  curRegState,
  getRegVal,
  setRegVal,
  addStmt,
  addAssignment,
  addExpr,
  finishWithTerminator,
  asAtomicStateUpdate,
  -- * State access
  getRegs,
  getCurrentIP,
  -- * Monad
  GenCont,
  Generator,
  runGenerator,
  shiftGen,
  unfinishedBlock,
  -- * Errors
  GeneratorError(..)
  ) where

import           GHC.TypeLits

import           Control.Lens
import qualified Control.Monad.Cont as Ct
import qualified Control.Monad.Except as ET
import qualified Control.Monad.Fail as MF
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
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as NC

import           Data.Macaw.SemMC.Simplify ( simplifyValue, simplifyApp )

data Expr arch ids tp where
  ValueExpr :: !(Value arch ids tp) -> Expr arch ids tp
  AppExpr   :: !(App (Value arch ids) tp) -> Expr arch ids tp

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

-- | Get the value of a machine register (in the 'Generator' state).
getRegVal :: OrdF (ArchReg arch)
          => ArchReg arch tp
          -> Generator arch ids s (Value arch ids tp)
getRegVal reg = do
  genState <- St.get
  return (genState ^. curRegState . boundValue reg)

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

data PartialBlock arch ids where
  UnfinishedPartialBlock :: !(PreBlock arch ids) -> PartialBlock arch ids
  FinishedPartialBlock :: !(Block arch ids) -> PartialBlock arch ids

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
  Generator { runG :: Ct.ContT (PartialBlock arch ids)
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
#if !(MIN_VERSION_base(4,13,0))
  fail = MF.fail
#endif

instance St.MonadState (GenState arch ids s) (Generator arch ids s) where
  get = Generator Rd.ask
  put nextState = Generator $ Ct.ContT $ \c -> Rd.ReaderT $ \_s ->
    Rd.runReaderT (c ()) nextState

instance ET.MonadError GeneratorError (Generator arch ids s) where
  throwError e = Generator (Ct.ContT (\_ -> ET.throwError e))

instance MF.MonadFail (Generator arch ids s) where
  fail err = ET.throwError $ GeneratorMessage $ show err

-- | The type of continuations provided by 'shiftGen'
type GenCont arch ids s a = a -> GenState arch ids s -> ET.ExceptT GeneratorError (ST s) (PartialBlock arch ids)

-- | Given a final continuation to call, run the generator (and produce a final
-- result with the given continuation @k@).  Also takes an initial state.
runGenerator :: GenCont arch ids s a
             -> GenState arch ids s
             -> Generator arch ids s a
             -> ET.ExceptT GeneratorError (ST s) (PartialBlock arch ids)
runGenerator k st (Generator m) = Rd.runReaderT (Ct.runContT m (Rd.ReaderT . k)) st

-- | Capture the current continuation and execute an action that gets that
-- continuation as an argument (it can be invoked as many times as desired).
shiftGen :: (GenCont arch ids s a -> GenState arch ids s -> ET.ExceptT GeneratorError (ST s) (PartialBlock arch ids))
         -> Generator arch ids s a
shiftGen f =
  Generator $ Ct.ContT $ \k -> Rd.ReaderT $ \s -> f (Rd.runReaderT . k) s

unfinishedBlock :: (Monad m) => a -> GenState arch ids s -> m (PartialBlock arch ids)
unfinishedBlock _ s = return (UnfinishedPartialBlock (s ^. blockState))

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
--
-- NOTE: This should be called at most once, right at the beginning of
-- semantics transformers, to get a snapshot of the register state before the
-- instruction modifies them. If it is called later, it will return
-- partially-modified register values, which is probably not what you want.
getRegs :: Generator arch ids s (RegState (ArchReg arch) (Value arch ids))
getRegs = do
  genState <- St.get
  return (genState ^. (blockState . pBlockState))

-- | Get the current value of the IP (NOT the snapshot of the value from when
-- the instruction began evaluating).
getCurrentIP ::
  (OrdF (ArchReg arch), RegisterInfo (ArchReg arch)) =>
  Generator arch ids s (BVValue arch ids (ArchAddrWidth arch))
getCurrentIP = do
  regs <- getRegs
  return (regs ^. boundValue ip_reg)

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
  return $! FinishedPartialBlock fin_block

-- | Convert the contents of a 'PreBlock' (a block being constructed) into a
-- full-fledged 'Block'
--
-- The @term@ function is used to create the terminator statement of the block.
finishBlock' :: PreBlock arch ids
             -> (RegState (ArchReg arch) (Value arch ids) -> TermStmt arch ids)
             -> Block arch ids
finishBlock' preBlock term =
  Block { blockStmts = F.toList (preBlock ^. pBlockStmts)
        , blockTerm = term (preBlock ^. pBlockState)
        }

