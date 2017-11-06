{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.PPC.Generator (
  GenResult(..),
  GenState(..),
  initGenState,
  initRegState,
  PPCGenerator,
  GenCont,
  runGenerator,
  genResult,
  Expr(..),
  BlockSeq(..),
  PreBlock(..),
  addStmt,
  addAssignment,
  getReg,
  getRegValue,
  shiftGen,
  finishBlock,
  finishBlock',
  finishWithTerminator,
  -- * Lenses
  blockState,
  curPPCState,
  pBlockStmts,
  pBlockState,
  frontierBlocks,
  blockSeq,
  -- * Constraints
  PPCArchConstraints,
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
import qualified Data.Sequence as Seq
import           Data.Word (Word64)

import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Nonce as NC

import qualified SemMC.Architecture.PPC.Location as APPC

import           Data.Macaw.PPC.PPCReg
import           Data.Macaw.PPC.Arch ( PPCArchConstraints )

-- GenResult

data GenResult ppc ids =
  GenResult { resBlockSeq :: BlockSeq ppc ids
            , resState :: Maybe (PreBlock ppc ids)
            }

------------------------------------------------------------------------
-- Expr

data Expr ppc ids tp where
  ValueExpr :: !(Value ppc ids tp) -> Expr ppc ids tp
  AppExpr   :: !(App (Value ppc ids) tp) -> Expr ppc ids tp
------------------------------------------------------------------------
-- BlockSeq
data BlockSeq ppc ids = BlockSeq
  { nextBlockID :: !Word64
    -- ^ index of next block
  , _frontierBlocks :: !(Seq.Seq (Block ppc ids))
    -- ^ Blocks added to CFG
  }

deriving instance Show (Block ppc ids) => Show (BlockSeq ppc ids)
deriving instance (PPCArchConstraints ppc) => Show (Block ppc ids)
deriving instance (PPCArchConstraints ppc) => Show (TermStmt ppc ids)

-- | Control flow blocs generated so far.
-- nextBlockID :: Simple Lens (BlockSeq ppc s) Word64
-- nextBlockID = lens _nextBlockID (\s v -> s { _nextBlockID = v })

-- | Blocks that are not in CFG that end with a FetchAndExecute,
-- which we need to analyze to compute new potential branch targets.
frontierBlocks :: Simple Lens (BlockSeq ppc s) (Seq.Seq (Block ppc s))
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

data GenState ppc ids s =
  GenState { assignIdGen :: !(NC.NonceGenerator (ST s) ids)
           , _blockSeq :: !(BlockSeq ppc ids)
           , _blockState :: !(PreBlock ppc ids)
           , genAddr :: !(MM.MemSegmentOff (ArchAddrWidth ppc))
           }

initGenState :: NC.NonceGenerator (ST s) ids
             -> MM.MemSegmentOff (ArchAddrWidth ppc)
             -> RegState (PPCReg ppc) (Value ppc ids)
             -> GenState ppc ids s
initGenState nonceGen addr st =
  GenState { assignIdGen = nonceGen
           , _blockSeq = BlockSeq { nextBlockID = 0, _frontierBlocks = Seq.empty }
           , _blockState = emptyPreBlock st 0 addr
           , genAddr = addr
           }

initRegState :: ( KnownNat (RegAddrWidth (PPCReg ppc))
                , ArchReg ppc ~ PPCReg ppc
                , 1 <= RegAddrWidth (PPCReg ppc)
                , MM.MemWidth (RegAddrWidth (PPCReg ppc))
                , ArchWidth ppc)
             => ArchSegmentOff ppc
             -> RegState (PPCReg ppc) (Value ppc ids)
initRegState startIP = mkRegState Initial
                     & curIP .~ RelocatableValue NR.knownNat (MM.relativeSegmentAddr startIP)

emptyPreBlock :: RegState (PPCReg ppc) (Value ppc ids)
              -> Word64
              -> MM.MemSegmentOff (RegAddrWidth (ArchReg ppc))
              -> PreBlock ppc ids
emptyPreBlock s0 idx addr =
  PreBlock { pBlockIndex = idx
           , pBlockAddr = addr
           , _pBlockStmts = Seq.empty
           , _pBlockState = s0
           , pBlockApps = MapF.empty
           }

blockSeq :: Simple Lens (GenState ppc ids s) (BlockSeq ppc ids)
blockSeq = lens _blockSeq (\s v -> s { _blockSeq = v })

blockState :: Simple Lens (GenState ppc ids s) (PreBlock ppc ids)
blockState = lens _blockState (\s v -> s { _blockState = v })

curPPCState :: Simple Lens (GenState ppc ids s) (RegState (PPCReg ppc) (Value ppc ids))
curPPCState = blockState . pBlockState

------------------------------------------------------------------------
-- PPCGenerator

data GeneratorError = InvalidEncoding
                    | GeneratorMessage String
  deriving (Show)

newtype PPCGenerator ppc ids s a =
  PPCGenerator { runG :: Ct.ContT (GenResult ppc ids)
                                  (Rd.ReaderT (GenState ppc ids s)
                                              (ET.ExceptT GeneratorError (ST s))) a }
                             deriving (Applicative,
                                       Functor,
                                       Rd.MonadReader (GenState ppc ids s),
                                       Ct.MonadCont)

instance Monad (PPCGenerator ppc ids s) where
  return v = PPCGenerator (return v)
  PPCGenerator m >>= h = PPCGenerator (m >>= \v -> runG (h v))
  PPCGenerator m >> PPCGenerator n = PPCGenerator (m >> n)
  fail msg = PPCGenerator (Ct.ContT (\_ -> ET.throwError (GeneratorMessage msg)))

instance St.MonadState (GenState ppc ids s) (PPCGenerator ppc ids s) where
  get = PPCGenerator Rd.ask
  put nextState = PPCGenerator $ Ct.ContT $ \c -> Rd.ReaderT $ \_s ->
    Rd.runReaderT (c ()) nextState

instance ET.MonadError GeneratorError (PPCGenerator ppc ids s) where
  throwError e = PPCGenerator (Ct.ContT (\_ -> ET.throwError e))
  -- catchError a hdlr = do
  --   r <- liftST $ ET.runExceptT (unDisM a)
  --   case r of
  --     Left l -> do
  --       r' <- liftST $ ET.runExceptT (unDisM (hdlr l))
  --       case r' of
  --         Left e -> DisM (ET.throwError e)
  --         Right res -> return res
  --     Right res -> return res

type GenCont ppc ids s a = a -> GenState ppc ids s -> ET.ExceptT GeneratorError (ST s) (GenResult ppc ids)

runGenerator :: GenCont ppc ids s a
             -> GenState ppc ids s
             -> PPCGenerator ppc ids s a
             -> ST s (Either GeneratorError (GenResult ppc ids))
runGenerator k st (PPCGenerator m) = ET.runExceptT (Rd.runReaderT (Ct.runContT m (Rd.ReaderT . k)) st)

shiftGen :: (GenCont ppc ids s a -> GenState ppc ids s -> ET.ExceptT GeneratorError (ST s) (GenResult ppc ids))
         -> PPCGenerator ppc ids s a
shiftGen f =
  PPCGenerator $ Ct.ContT $ \k -> Rd.ReaderT $ \s -> f (Rd.runReaderT . k) s

genResult :: (Monad m) => a -> GenState ppc ids s -> m (GenResult ppc ids)
genResult _ s = do
  return GenResult { resBlockSeq = s ^. blockSeq
                   , resState = Just (s ^. blockState)
                   }

addStmt :: (ArchConstraints ppc) => Stmt ppc ids -> PPCGenerator ppc ids s ()
addStmt stmt = (blockState . pBlockStmts) %= (Seq.|> stmt)

newAssignId :: PPCGenerator ppc ids s (AssignId ids tp)
newAssignId = do
  nonceGen <- St.gets assignIdGen
  n <- liftST $ NC.freshNonce nonceGen
  return (AssignId n)

liftST :: ST s a -> PPCGenerator ppc ids s a
liftST = PPCGenerator . lift . lift . lift

addAssignment :: ArchConstraints ppc
              => AssignRhs ppc ids tp
              -> PPCGenerator ppc ids s (Assignment ppc ids tp)
addAssignment rhs = do
  l <- newAssignId
  let a = Assignment l rhs
  addStmt $ AssignStmt a
  return a

getReg :: PPCReg ppc tp -> PPCGenerator ppc ids s (Expr ppc ids tp)
getReg r = do
  genState <- St.get
  let expr = ValueExpr (genState ^. blockState ^. pBlockState ^. boundValue r)
  return expr

getRegValue :: PPCReg ppc tp -> PPCGenerator ppc ids s (Value ppc ids tp)
getRegValue r = do
  genState <- St.get
  return (genState ^. blockState ^. pBlockState ^. boundValue r)

-- | Finish a block immediately with the given terminator statement
--
-- This uses the underlying continuation monad to skip the normal
-- post-instruction behavior.
--
-- NOTE: We do not do an explicit instruction pointer update; the handler for
-- architecture-specific terminator statements handles that.
finishWithTerminator :: forall ppc ids s a
                      . (PPCArchConstraints ppc, KnownNat (APPC.ArchRegWidth ppc))
                     => (RegState (PPCReg ppc) (Value ppc ids) -> TermStmt ppc ids)
                     -> PPCGenerator ppc ids s a
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
finishBlock' :: PreBlock ppc ids
             -> (RegState (PPCReg ppc) (Value ppc ids) -> TermStmt ppc ids)
             -> Block ppc ids
finishBlock' preBlock term =
  Block { blockLabel = pBlockIndex preBlock
        , blockStmts = F.toList (preBlock ^. pBlockStmts)
        , blockTerm = term (preBlock ^. pBlockState)
        }

-- | Consume a 'GenResult', finish off the contained 'PreBlock', and append the
-- new block to the block frontier.
finishBlock :: (RegState (PPCReg ppc) (Value ppc ids) -> TermStmt ppc ids)
            -> GenResult ppc ids
            -> BlockSeq ppc ids
finishBlock term st =
  case resState st of
    Nothing -> resBlockSeq st
    Just preBlock ->
      let b = finishBlock' preBlock term
      in resBlockSeq st & frontierBlocks %~ (Seq.|> b)
