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
  simplifyCurrentBlock,
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
import           Control.Monad (forM_)
import           Debug.Trace
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
import           Data.Macaw.CFG.Rewriter
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.Nonce as NC

import qualified SemMC.Architecture.PPC.Location as APPC

import           Data.Macaw.PPC.PPCReg
import           Data.Macaw.PPC.Arch ( rewritePrimFn
                                     , PPCArchConstraints)

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
  { nextBlockID :: !Word64
    -- ^ index of next block
  , _frontierBlocks :: !(Seq.Seq (Block ppc s))
    -- ^ Blocks added to CFG
  }

deriving instance Show (Block ppc s) => Show (BlockSeq ppc s)
deriving instance (PPCArchConstraints ppc) => Show (Block ppc s)
deriving instance (PPCArchConstraints ppc) => Show (TermStmt ppc s)

-- | Control flow blocs generated so far.
-- nextBlockID :: Simple Lens (BlockSeq ppc s) Word64
-- nextBlockID = lens _nextBlockID (\s v -> s { _nextBlockID = v })

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
           , _blockSeq :: !(BlockSeq ppc s)
           , _blockState :: !(PreBlock ppc s)
           , genAddr :: !(MM.MemSegmentOff (ArchAddrWidth ppc))
           }

initGenState :: NC.NonceGenerator (ST s) s
             -> MM.MemSegmentOff (ArchAddrWidth ppc)
             -> RegState (PPCReg ppc) (Value ppc s)
             -> GenState ppc s
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

blockSeq :: Simple Lens (GenState ppc s) (BlockSeq ppc s)
blockSeq = lens _blockSeq (\s v -> s { _blockSeq = v })

blockState :: Simple Lens (GenState ppc s) (PreBlock ppc s)
blockState = lens _blockState (\s v -> s { _blockState = v })

curPPCState :: Simple Lens (GenState ppc s) (RegState (PPCReg ppc) (Value ppc s))
curPPCState = blockState . pBlockState

------------------------------------------------------------------------
-- PPCGenerator

data GeneratorError = InvalidEncoding
                    | GeneratorMessage String
  deriving (Show)

newtype PPCGenerator ppc s a =
  PPCGenerator { runG :: Ct.ContT (GenResult ppc s)
                                  (Rd.ReaderT (GenState ppc s)
                                              (ET.ExceptT GeneratorError (ST s))) a }
                             deriving (Applicative,
                                       Functor,
                                       Rd.MonadReader (GenState ppc s),
                                       Ct.MonadCont)

instance Monad (PPCGenerator ppc s) where
  return v = PPCGenerator (return v)
  PPCGenerator m >>= h = PPCGenerator (m >>= \v -> runG (h v))
  PPCGenerator m >> PPCGenerator n = PPCGenerator (m >> n)
  fail msg = PPCGenerator (Ct.ContT (\_ -> ET.throwError (GeneratorMessage msg)))

instance St.MonadState (GenState ppc s) (PPCGenerator ppc s) where
  get = PPCGenerator Rd.ask
  put nextState = PPCGenerator $ Ct.ContT $ \c -> Rd.ReaderT $ \_s ->
    Rd.runReaderT (c ()) nextState

instance ET.MonadError GeneratorError (PPCGenerator ppc s) where
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

type GenCont ppc s a = a -> GenState ppc s -> ET.ExceptT GeneratorError (ST s) (GenResult ppc s)

runGenerator :: GenCont ppc s a
             -> GenState ppc s
             -> PPCGenerator ppc s a
             -> ST s (Either GeneratorError (GenResult ppc s))
runGenerator k st (PPCGenerator m) = ET.runExceptT (Rd.runReaderT (Ct.runContT m (Rd.ReaderT . k)) st)

shiftGen :: (GenCont ppc s a -> GenState ppc s -> ET.ExceptT GeneratorError (ST s) (GenResult ppc s))
         -> PPCGenerator ppc s a
shiftGen f =
  PPCGenerator $ Ct.ContT $ \k -> Rd.ReaderT $ \s -> f (Rd.runReaderT . k) s

genResult :: (Monad m) => a -> GenState ppc s -> m (GenResult ppc s)
genResult _ s = do
  return GenResult { resBlockSeq = s ^. blockSeq
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
liftST = PPCGenerator . lift . lift . lift

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

-- | Finish a block immediately with the given terminator statement
--
-- This uses the underlying continuation monad to skip the normal
-- post-instruction behavior.
--
-- NOTE: We have to do an explicit instruction pointer update so that macaw
-- knows to analyze starting at the next instruction (and doesn't treat the
-- terminator as its own basic block).
--
-- Other instructions handle their own IP updates explicitly.
finishWithTerminator :: forall ppc s a
                      . (PPCArchConstraints ppc, KnownNat (APPC.ArchRegWidth ppc))
                     => (RegState (PPCReg ppc) (Value ppc s) -> TermStmt ppc s)
                     -> PPCGenerator ppc s a
finishWithTerminator term = do
  oldIP <- getRegValue PPC_IP
  newIPAssign <- addAssignment $ EvalApp (BVAdd ptrRep oldIP (BVValue ptrRep 0x4))
  blockState . pBlockState . boundValue PPC_IP .= AssignedValue newIPAssign
  shiftGen $ \_ s0 -> do
    let pre_block = s0 ^. blockState
    let fin_block = finishBlock' pre_block term
    return GenResult { resBlockSeq = s0 ^. blockSeq & frontierBlocks %~ (Seq.|> fin_block)
                     , resState = Nothing
                     }
  where
    ptrRep :: NR.NatRepr (RegAddrWidth (PPCReg ppc))
    ptrRep = NR.knownNat

-- | Convert the contents of a 'PreBlock' (a block being constructed) into a
-- full-fledged 'Block'
--
-- The @term@ function is used to create the terminator statement of the block.
finishBlock' :: PreBlock ppc s
             -> (RegState (PPCReg ppc) (Value ppc s) -> TermStmt ppc s)
             -> Block ppc s
finishBlock' preBlock term =
  Block { blockLabel = pBlockIndex preBlock
        , blockStmts = F.toList (preBlock ^. pBlockStmts)
        , blockTerm = term (preBlock ^. pBlockState)
        }

-- | Consume a 'GenResult', finish off the contained 'PreBlock', and append the
-- new block to the block frontier.
finishBlock :: (RegState (PPCReg ppc) (Value ppc s) -> TermStmt ppc s)
            -> GenResult ppc s
            -> BlockSeq ppc s
finishBlock term st =
  case resState st of
    Nothing -> resBlockSeq st
    Just preBlock ->
      let b = finishBlock' preBlock term
      in resBlockSeq st & frontierBlocks %~ (Seq.|> b)


-- terminateBlocks :: (RegState (PPCReg ppc) (Value ppc s) -> TermStmt ppc s)
--                 ->

simplifyCurrentBlock
  :: forall ppc s . PPCArchConstraints ppc => PPCGenerator ppc s ()
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
