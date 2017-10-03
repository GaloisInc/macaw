{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Macaw.PPC.Generator (
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

------------------------------------------------------------------------
-- Expr

data Expr ppc ids tp where
  ValueExpr :: !(Value ppc ids tp) -> Expr ppc ids tp
  AppExpr   :: !(App (Expr ppc ids) tp) -> Expr ppc ids tp

------------------------------------------------------------------------
-- BlockSeq
data BlockSeq ppc ids = BlockSeq
  { _nextBlockID :: !Word64
    -- ^ index of next block
  , _frontierBlocks :: !(Seq.Seq (Block ppc ids))
    -- ^ Blocks added to CFG
  }

-- | Control flow blocs generated so far.
nextBlockID :: Simple Lens (BlockSeq ppc ids) Word64
nextBlockID = lens _nextBlockID (\s v -> s { _nextBlockID = v })

-- | Blocks that are not in CFG that end with a FetchAndExecute,
-- which we need to analyze to compute new potential branch targets.
frontierBlocks :: Simple Lens (BlockSeq ppc ids) (Seq.Seq (Block ppc ids))
frontierBlocks = lens _frontierBlocks (\s v -> s { _frontierBlocks = v })

------------------------------------------------------------------------
-- PreBlock

data PreBlock ppc ids = PreBlock { pBlockIndex :: !Word64
                                  , pBlockAddr  :: !(MM.MemSegmentOff (ArchAddrWidth ppc))
                                  -- ^ Starting address of function in preblock.
                                  , _pBlockStmts :: !(Seq.Seq (Stmt ppc ids))
                                  , _pBlockState :: !(RegState (PPCReg ppc) (Value ppc ids))
                                  , pBlockApps  :: !(MapF.MapF (App (Value ppc ids)) (Assignment ppc ids))
                                  }

pBlockStmts :: Simple Lens (PreBlock ppc ids) (Seq.Seq (Stmt ppc ids))
pBlockStmts = lens _pBlockStmts (\s v -> s { _pBlockStmts = v })

pBlockState :: Simple Lens (PreBlock ppc ids) (RegState (PPCReg ppc) (Value ppc ids))
pBlockState = lens _pBlockState (\s v -> s { _pBlockState = v })

------------------------------------------------------------------------
-- GenState

data GenState ppc s ids =
  GenState { assignIdGen :: !(NC.NonceGenerator (ST s) ids)
           , blockSeq :: !(BlockSeq ppc ids)
           , _blockState :: !(PreBlock ppc ids)
           , genAddr :: !(MM.MemSegmentOff (ArchAddrWidth ppc))
           }

initGenState :: NC.NonceGenerator (ST s) ids
             -> MM.MemSegmentOff (ArchAddrWidth ppc)
             -> GenState ppc s ids
initGenState nonceGen addr =
  GenState { assignIdGen = nonceGen
           , blockSeq = BlockSeq { _nextBlockID = 0, _frontierBlocks = Seq.empty }
           , _blockState = undefined
           , genAddr = addr
           }

blockState :: Simple Lens (GenState ppc s ids) (PreBlock ppc ids)
blockState = lens _blockState (\s v -> s { _blockState = v })

curPPCState :: Simple Lens (GenState ppc s ids) (RegState (PPCReg ppc) (Value ppc ids))
curPPCState = blockState . pBlockState

------------------------------------------------------------------------
-- PPCGenerator

newtype PPCGenerator ppc s ids a = PPCGenerator { runGen :: St.StateT (GenState ppc s ids) (ST s) a }
  deriving (Monad,
            Functor,
            Applicative,
            St.MonadState (GenState ppc s ids))

runGenerator :: GenState ppc s ids -> PPCGenerator ppc s ids a -> ST s (a, GenState ppc s ids)
runGenerator s0 act = St.runStateT (runGen act) s0

execGenerator :: GenState ppc s ids -> PPCGenerator ppc s ids () -> ST s (GenState ppc s ids)
execGenerator s0 act = St.execStateT (runGen act) s0

-- Given a stateful computation on the underlying GenState, create a PPCGenerator
-- that runs that same computation.
modGenState :: St.State (GenState ppc s ids) a -> PPCGenerator ppc s ids a
modGenState m = PPCGenerator $ St.StateT $ \genState -> do
  return $ St.runState m genState

addStmt :: Stmt ppc ids -> PPCGenerator ppc s ids ()
addStmt stmt = (blockState . pBlockStmts) %= (Seq.|> stmt)

newAssignId :: PPCGenerator ppc s ids (AssignId ids tp)
newAssignId = do
  nonceGen <- St.gets assignIdGen
  n <- liftST $ NC.freshNonce nonceGen
  return (AssignId n)

liftST :: ST s a -> PPCGenerator ppc s ids a
liftST = PPCGenerator . lift

addAssignment :: AssignRhs ppc ids tp
              -> PPCGenerator ppc s ids (Assignment ppc ids tp)
addAssignment rhs = do
  l <- newAssignId
  let a = Assignment l rhs
  addStmt $ AssignStmt a
  return a

getReg :: PPCReg ppc tp -> PPCGenerator ppc s ids (Expr ppc ids tp)
getReg r = PPCGenerator $ St.StateT $ \genState -> do
  let expr = ValueExpr (genState ^. blockState ^. pBlockState ^. boundValue r)
  return (expr, genState)
