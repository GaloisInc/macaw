{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Macaw.PPC.Generator (
  GenResult(..),
  GenState,
  initGenState,
  PPCGenerator,
  runGenerator,
  execGenerator,
  Expr(..),
  BlockSeq(..),
  PreBlock(..),
  addStmt,
  addAssignment,
  getReg,
  blockSeq,
  -- * Lenses
  blockState,
  curPPCState,
  pBlockStmts,
  pBlockState,
  frontierBlocks
  ) where

import           Control.Lens
import           Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )
import qualified Control.Monad.State.Strict as St
import qualified Data.Sequence as Seq
import           Data.Word (Word64)

import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as NC

import           Data.Macaw.PPC.PPCReg

-- GenResult

data GenResult ppc s =
  GenResult { resBlockSeq :: BlockSeq ppc s
            , resState :: Maybe (PreBlock ppc s)
            }

------------------------------------------------------------------------
-- Expr

data Expr ppc ids tp where
  ValueExpr :: !(Value ppc s tp) -> Expr ppc s tp
  AppExpr   :: !(App (Expr ppc s) tp) -> Expr ppc s tp

------------------------------------------------------------------------
-- BlockSeq
data BlockSeq ppc s = BlockSeq
  { _nextBlockID :: !Word64
    -- ^ index of next block
  , _frontierBlocks :: !(Seq.Seq (Block ppc s))
    -- ^ Blocks added to CFG
  }

-- | Control flow blocs generated so far.
nextBlockID :: Simple Lens (BlockSeq ppc s) Word64
nextBlockID = lens _nextBlockID (\s v -> s { _nextBlockID = v })

-- | Blocks that are not in CFG that end with a FetchAndExecute,
-- which we need to analyze to compute new potential branch targets.
frontierBlocks :: Simple Lens (BlockSeq ppc s) (Seq.Seq (Block ppc s))
frontierBlocks = lens _frontierBlocks (\s v -> s { _frontierBlocks = v })

------------------------------------------------------------------------
-- PreBlock

data PreBlock ppc s = PreBlock { pBlockIndex :: !Word64
                               , pBlockAddr  :: !(MM.MemSegmentOff (ArchAddrWidth ppc))
                               -- ^ Starting address of function in preblock.
                               , _pBlockStmts :: !(Seq.Seq (Stmt ppc s))
                               , _pBlockState :: !(RegState (PPCReg ppc) (Value ppc s))
                               , pBlockApps  :: !(MapF.MapF (App (Value ppc s)) (Assignment ppc s))
                               }

pBlockStmts :: Simple Lens (PreBlock ppc s) (Seq.Seq (Stmt ppc s))
pBlockStmts = lens _pBlockStmts (\s v -> s { _pBlockStmts = v })

pBlockState :: Simple Lens (PreBlock ppc s) (RegState (PPCReg ppc) (Value ppc s))
pBlockState = lens _pBlockState (\s v -> s { _pBlockState = v })

------------------------------------------------------------------------
-- GenState

data GenState ppc s =
  GenState { assignIdGen :: !(NC.NonceGenerator (ST s) s)
           , blockSeq :: !(BlockSeq ppc s)
           , _blockState :: !(PreBlock ppc s)
           , genAddr :: !(MM.MemSegmentOff (ArchAddrWidth ppc))
           }

initGenState :: NC.NonceGenerator (ST s) s
             -> MM.MemSegmentOff (ArchAddrWidth ppc)
             -> GenState ppc s
initGenState nonceGen addr =
  GenState { assignIdGen = nonceGen
           , blockSeq = BlockSeq { _nextBlockID = 0, _frontierBlocks = Seq.empty }
           , _blockState = undefined
           , genAddr = addr
           }

blockState :: Simple Lens (GenState ppc s) (PreBlock ppc s)
blockState = lens _blockState (\s v -> s { _blockState = v })

curPPCState :: Simple Lens (GenState ppc s) (RegState (PPCReg ppc) (Value ppc s))
curPPCState = blockState . pBlockState

------------------------------------------------------------------------
-- PPCGenerator

newtype PPCGenerator ppc s a = PPCGenerator { runGen :: St.StateT (GenState ppc s) (ST s) a }
  deriving (Monad,
            Functor,
            Applicative,
            St.MonadState (GenState ppc s))

runGenerator :: GenState ppc s -> PPCGenerator ppc s a -> ST s (a, GenState ppc s)
runGenerator s0 act = St.runStateT (runGen act) s0

execGenerator :: GenState ppc s -> PPCGenerator ppc s () -> ST s (GenState ppc s)
execGenerator s0 act = St.execStateT (runGen act) s0

-- Given a stateful computation on the underlying GenState, create a PPCGenerator
-- that runs that same computation.
modGenState :: St.State (GenState ppc s) a -> PPCGenerator ppc s a
modGenState m = PPCGenerator $ St.StateT $ \genState -> do
  return $ St.runState m genState

addStmt :: Stmt ppc s -> PPCGenerator ppc s ()
addStmt stmt = (blockState . pBlockStmts) %= (Seq.|> stmt)

newAssignId :: PPCGenerator ppc s (AssignId s tp)
newAssignId = do
  nonceGen <- St.gets assignIdGen
  n <- liftST $ NC.freshNonce nonceGen
  return (AssignId n)

liftST :: ST s a -> PPCGenerator ppc s a
liftST = PPCGenerator . lift

addAssignment :: AssignRhs ppc s tp
              -> PPCGenerator ppc s (Assignment ppc s tp)
addAssignment rhs = do
  l <- newAssignId
  let a = Assignment l rhs
  addStmt $ AssignStmt a
  return a

getReg :: PPCReg ppc tp -> PPCGenerator ppc s (Expr ppc s tp)
getReg r = PPCGenerator $ St.StateT $ \genState -> do
  let expr = ValueExpr (genState ^. blockState ^. pBlockState ^. boundValue r)
  return (expr, genState)
