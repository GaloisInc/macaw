{-# LANGUAGE DataKinds #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeOperators #-}
module Data.Macaw.PPC.Generator (
  GenResult(..),
  GenState(..),
  initGenState,
  initRegState,
  PPCGenerator,
  runGenerator,
  execGenerator,
  evalGenerator,
  genResult,
  Expr(..),
  BlockSeq(..),
  PreBlock(..),
  addStmt,
  addAssignment,
  getReg,
  getRegValue,
  simplifyCurrentBlock,
  -- * Lenses
  blockState,
  curPPCState,
  pBlockStmts,
  pBlockState,
  frontierBlocks,
  -- * Constraints
  PPCArchConstraints,
  -- * Errors
  GeneratorError(..)
  ) where

import           GHC.TypeLits
import           Control.Monad (forM_)
import           Debug.Trace
import           Control.Lens
import           Data.Parameterized.TraversableFC
import qualified Control.Monad.Except as ET
import           Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )
import qualified Control.Monad.State.Strict as St
import qualified Data.Sequence as Seq
import           Data.Word (Word64)

import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import           Data.Macaw.CFG.Rewriter
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Nonce as NC

import           Data.Macaw.PPC.PPCReg
import           Data.Macaw.PPC.Arch (rewritePrimFn, PPCPrimFn, PPCArch, PPCArchStmt)

import Debug.Trace (trace)

-- GenResult

data GenResult ppc s =
  GenResult { resBlockSeq :: BlockSeq ppc s
            , resState :: Maybe (PreBlock ppc s)
            }

------------------------------------------------------------------------
-- Expr

data Expr ppc s tp where
  ValueExpr :: !(Value ppc s tp) -> Expr ppc s tp
--   AppExpr   :: !(App (Value ppc s) tp) -> Expr ppc s tp
  AppExpr   :: !(App (Value ppc s) tp) -> Expr ppc s tp
------------------------------------------------------------------------
-- BlockSeq
data BlockSeq ppc s = BlockSeq
  { _nextBlockID :: !Word64
    -- ^ index of next block
  , _frontierBlocks :: !(Seq.Seq (Block ppc s))
    -- ^ Blocks added to CFG
  }

deriving instance Show (Block ppc s) => Show (BlockSeq ppc s)
deriving instance (PPCWidth ppc, PPCArch ppc) => Show (Block ppc s)
deriving instance (PPCWidth ppc, PPCArch ppc) => Show (TermStmt ppc s)

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
             -> RegState (PPCReg ppc) (Value ppc s)
             -> GenState ppc s
initGenState nonceGen addr st =
  GenState { assignIdGen = nonceGen
           , blockSeq = BlockSeq { _nextBlockID = 0, _frontierBlocks = Seq.empty }
           , _blockState = emptyPreBlock st 0 addr
           , genAddr = addr
           }

initRegState :: (KnownNat (RegAddrWidth (PPCReg ppc)), ArchReg ppc ~ PPCReg ppc, 1 <= RegAddrWidth (PPCReg ppc), MM.MemWidth (RegAddrWidth (PPCReg ppc)), ArchWidth ppc)
             => ArchSegmentOff ppc
             -> RegState (PPCReg ppc) (Value ppc s)
initRegState startIP = mkRegState Initial
                     & curIP .~ RelocatableValue NR.knownNat (MM.relativeSegmentAddr startIP)

emptyPreBlock :: RegState (PPCReg ppc) (Value ppc s)
              -> Word64
              -> MM.MemSegmentOff (RegAddrWidth (ArchReg ppc))
              -> PreBlock ppc s
emptyPreBlock s0 idx addr =
  PreBlock { pBlockIndex = idx
           , pBlockAddr = addr
           , _pBlockStmts = Seq.empty
           , _pBlockState = s0
           , pBlockApps = MapF.empty
           }

blockState :: Simple Lens (GenState ppc s) (PreBlock ppc s)
blockState = lens _blockState (\s v -> s { _blockState = v })

curPPCState :: Simple Lens (GenState ppc s) (RegState (PPCReg ppc) (Value ppc s))
curPPCState = blockState . pBlockState

------------------------------------------------------------------------
-- PPCGenerator

data GeneratorError = InvalidEncoding
  deriving (Show)

newtype PPCGenerator ppc s a = PPCGenerator { runGen :: St.StateT (GenState ppc s) (ET.ExceptT GeneratorError (ST s)) a }
  deriving (Monad,
            Functor,
            Applicative,
            ET.MonadError GeneratorError,
            St.MonadState (GenState ppc s))

runGenerator :: GenState ppc s -> PPCGenerator ppc s a -> ST s (Either GeneratorError (a, GenState ppc s))
runGenerator s0 act = ET.runExceptT (St.runStateT (runGen act) s0)

execGenerator :: GenState ppc s -> PPCGenerator ppc s () -> ST s (Either GeneratorError (GenState ppc s))
execGenerator s0 act = ET.runExceptT (St.execStateT (runGen act) s0)

evalGenerator :: GenState ppc s -> PPCGenerator ppc s a -> ST s (Either GeneratorError a)
evalGenerator s0 act = ET.runExceptT (St.evalStateT (runGen act) s0)

genResult :: PPCGenerator ppc s (GenResult ppc s)
genResult = do
  s <- St.get
  return GenResult { resBlockSeq = blockSeq s
                   , resState = Just (s ^. blockState)
                   }

addStmt :: (ArchConstraints ppc) => Stmt ppc s -> PPCGenerator ppc s ()
addStmt stmt = (blockState . pBlockStmts) %= (Seq.|> stmt)

newAssignId :: PPCGenerator ppc s (AssignId s tp)
newAssignId = do
  nonceGen <- St.gets assignIdGen
  n <- liftST $ NC.freshNonce nonceGen
  return (AssignId n)

liftST :: ST s a -> PPCGenerator ppc s a
liftST = PPCGenerator . lift . lift

addAssignment :: ArchConstraints ppc
              => AssignRhs ppc s tp
              -> PPCGenerator ppc s (Assignment ppc s tp)
addAssignment rhs = do
  l <- newAssignId
  let a = Assignment l rhs
  addStmt $ AssignStmt a
  return a

getReg :: PPCReg ppc tp -> PPCGenerator ppc s (Expr ppc s tp)
getReg r = do
  genState <- St.get
  let expr = ValueExpr (genState ^. blockState ^. pBlockState ^. boundValue r)
  return expr

getRegValue :: PPCReg ppc tp -> PPCGenerator ppc s (Value ppc s tp)
getRegValue r = do
  genState <- St.get
  return (genState ^. blockState ^. pBlockState ^. boundValue r)

type PPCArchConstraints ppc s = ( ArchReg ppc ~ PPCReg ppc
                                , ArchFn ppc ~ PPCPrimFn ppc
                                , ArchStmt ppc ~ PPCArchStmt ppc
                                , ArchWidth ppc
                                , KnownNat (RegAddrWidth (PPCReg ppc))
                                , Show (Block ppc s)
                                , Show (BlockSeq ppc s)
                                , ArchConstraints ppc
                                )

simplifyCurrentBlock
  :: forall ppc s . PPCArchConstraints ppc s => PPCGenerator ppc s ()
simplifyCurrentBlock = do
  genState <- St.get
  let nonceGen = assignIdGen genState
      stmts = genState ^. blockState . pBlockStmts
      ctx = RewriteContext { rwctxNonceGen = nonceGen
                           , rwctxArchFn = rewritePrimFn
                           , rwctxArchStmt = appendRewrittenArchStmt
                           , rwctxConstraints = withConstraints
                           }
  (stmts', _) <- liftST $ runRewriter ctx $ do
    collectRewrittenStmts $ do
      forM_ stmts $ \stmt -> do
        traceShow stmt $ rewriteStmt stmt
  traceShow stmts' $ blockState . pBlockStmts .= Seq.fromList stmts'
  where withConstraints :: (forall a . (RegisterInfo (ArchReg ppc) => a) -> a)
        withConstraints x = x

-- eval :: Expr ppc s tp -> PPCGenerator ppc s (Value PPC s tp)
-- eval (ValueExpr v) = return v
-- eval (AppExpr a) = evalAp =<< traverseFC eval a





















