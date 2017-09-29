{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Macaw.PPC where

import Control.Lens
import Control.Monad.ST ( ST )
import Control.Monad.State.Strict
import qualified Data.Sequence as Seq
import Data.Word (Word64)

import Data.Macaw.Architecture.Info
import Data.Macaw.CFG
import Data.Macaw.Memory
import Data.Parameterized.Map as P
import Data.Parameterized.Nonce as P

import Data.Macaw.PPC.ArchTypes
import Data.Macaw.PPC.PPCReg

data Hole = Hole

------------------------------------------------------------------------
-- Expr

data Expr ids tp where
  ValueExpr :: !(Value PPC ids tp) -> Expr ids tp
  AppExpr   :: !(App (Expr ids) tp) -> Expr ids tp

------------------------------------------------------------------------
-- BlockSeq
data BlockSeq ids = BlockSeq
  { _nextBlockID :: !Word64
    -- ^ index of next block
  , _frontierBlocks :: !(Seq.Seq (Block PPC ids))
    -- ^ Blocks added to CFG
  }

-- | Control flow blocs generated so far.
nextBlockID :: Simple Lens (BlockSeq ids) Word64
nextBlockID = lens _nextBlockID (\s v -> s { _nextBlockID = v })

-- | Blocks that are not in CFG that end with a FetchAndExecute,
-- which we need to analyze to compute new potential branch targets.
frontierBlocks :: Simple Lens (BlockSeq ids) (Seq.Seq (Block PPC ids))
frontierBlocks = lens _frontierBlocks (\s v -> s { _frontierBlocks = v })

------------------------------------------------------------------------
-- PreBlock

data PreBlock ids = PreBlock { pBlockIndex :: !Word64
                             , pBlockAddr  :: !(MemSegmentOff 64)
                             -- ^ Starting address of function in preblock.
                             , _pBlockStmts :: !(Seq.Seq (Stmt PPC ids))
                             , pBlockState :: !(RegState PPCReg (Value PPC ids))
                             , pBlockApps  :: !(P.MapF (App (Value PPC ids)) (Assignment PPC ids))
                             }

pBlockStmts :: Simple Lens (PreBlock ids) (Seq.Seq (Stmt PPC ids))
pBlockStmts = lens _pBlockStmts (\s v -> s { _pBlockStmts = v })

------------------------------------------------------------------------
-- GenState

data GenState w s ids = GenState { assignIdGen :: !(P.NonceGenerator (ST s) ids)
                                 , blockSeq :: !(BlockSeq ids)
                                 , _blockState :: !(PreBlock ids)
                                 , genAddr :: !(MemSegmentOff w)
                                 }

blockState :: Simple Lens (GenState w s ids) (PreBlock ids)
blockState = lens _blockState (\s v -> s { _blockState = v })

------------------------------------------------------------------------
-- PPCGenerator

newtype PPCGenerator w s ids a = PPCGenerator { runGen :: StateT (GenState w s ids) (ST s) a }
  deriving (Monad,
            Functor,
            Applicative,
            MonadState (GenState w s ids))

-- Given a stateful computation on the underlying GenState, create a PPCGenerator
-- that runs that same computation.
modGenState :: State (GenState w s ids) a -> PPCGenerator w s ids a
modGenState m = PPCGenerator $ StateT $ \genState -> do
  return $ runState m genState

addStmt :: Stmt PPC ids -> PPCGenerator w s ids ()
addStmt stmt = PPCGenerator $ StateT $ \genState ->
  return ((), genState & (blockState . pBlockStmts %~ (Seq.|> stmt)))

ppc_linux_info :: ArchitectureInfo PPC
ppc_linux_info = undefined
