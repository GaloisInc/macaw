{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE ScopedTypeVariables #-}

module Data.Macaw.PPC (
  ppc_linux_info
  ) where

import Control.Lens
import Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )
import qualified Control.Monad.State.Strict as St
import qualified Data.Sequence as Seq
import           Data.Word (Word64)

import qualified Data.Macaw.Architecture.Info as MI
import Data.Macaw.AbsDomain.AbsState as MA
import Data.Macaw.CFG
import Data.Macaw.CFG.Block
import Data.Macaw.CFG.Core
import qualified Data.Macaw.CFG.DemandSet as MDS
import Data.Macaw.CFG.Rewriter
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Map as MapF
import qualified Data.Parameterized.Nonce as NC
import qualified Dismantle.PPC as D

import Data.Macaw.PPC.ArchTypes
import Data.Macaw.PPC.PPCReg

data Hole = Hole

-- A lot of the stuff in this file will ultimately be lifted into macaw-semmc.

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
                             , pBlockAddr  :: !(MM.MemSegmentOff 64)
                             -- ^ Starting address of function in preblock.
                             , _pBlockStmts :: !(Seq.Seq (Stmt PPC ids))
                             , _pBlockState :: !(RegState PPCReg (Value PPC ids))
                             , pBlockApps  :: !(MapF.MapF (App (Value PPC ids)) (Assignment PPC ids))
                             }

pBlockStmts :: Simple Lens (PreBlock ids) (Seq.Seq (Stmt PPC ids))
pBlockStmts = lens _pBlockStmts (\s v -> s { _pBlockStmts = v })

pBlockState :: Simple Lens (PreBlock ids) (RegState PPCReg (Value PPC ids))
pBlockState = lens _pBlockState (\s v -> s { _pBlockState = v })

------------------------------------------------------------------------
-- GenState

data GenState w s ids = GenState { assignIdGen :: !(NC.NonceGenerator (ST s) ids)
                                 , blockSeq :: !(BlockSeq ids)
                                 , _blockState :: !(PreBlock ids)
                                 , genAddr :: !(MM.MemSegmentOff w)
                                 }

blockState :: Simple Lens (GenState w s ids) (PreBlock ids)
blockState = lens _blockState (\s v -> s { _blockState = v })

curPPCState :: Simple Lens (GenState w s ids) (RegState PPCReg (Value PPC ids))
curPPCState = blockState . pBlockState

------------------------------------------------------------------------
-- PPCGenerator

newtype PPCGenerator w s ids a = PPCGenerator { runGen :: St.StateT (GenState w s ids) (ST s) a }
  deriving (Monad,
            Functor,
            Applicative,
            St.MonadState (GenState w s ids))

-- Given a stateful computation on the underlying GenState, create a PPCGenerator
-- that runs that same computation.
modGenState :: St.State (GenState w s ids) a -> PPCGenerator w s ids a
modGenState m = PPCGenerator $ St.StateT $ \genState -> do
  return $ St.runState m genState

addStmt :: Stmt PPC ids -> PPCGenerator w s ids ()
addStmt stmt = (blockState . pBlockStmts) %= (Seq.|> stmt)

newAssignId :: PPCGenerator w s ids (AssignId ids tp)
newAssignId = do
  nonceGen <- St.gets assignIdGen
  n <- liftST $ NC.freshNonce nonceGen
  return (AssignId n)

liftST :: ST s a -> PPCGenerator w s ids a
liftST = PPCGenerator . lift

addAssignment :: AssignRhs PPC ids tp
              -> PPCGenerator w s ids (Assignment PPC ids tp)
addAssignment rhs = do
  l <- newAssignId
  let a = Assignment l rhs
  addStmt $ AssignStmt a
  return a

getReg :: PPCReg tp -> PPCGenerator w s ids (Expr ids tp)
getReg r = PPCGenerator $ St.StateT $ \genState -> do
  let expr = ValueExpr (genState ^. blockState ^. pBlockState ^. boundValue r)
  return (expr, genState)

disassembleFn :: MM.Memory (ArchAddrWidth PPC)
              -> NC.NonceGenerator (ST ids) ids
              -> ArchSegmentOff PPC
              -> ArchAddrWord PPC
              -> MA.AbsBlockState (ArchReg PPC)
              -- ^ NOTE: We are leaving the type function ArchReg here because
              -- we need to generalize over PPC64 vs PPC32
              -> ST ids ([Block PPC ids], MM.MemWord (ArchAddrWidth PPC), Maybe String)
disassembleFn = undefined

preserveRegAcrossSyscall :: ArchReg PPC tp -> Bool
preserveRegAcrossSyscall = undefined

mkInitialAbsState :: MM.Memory (RegAddrWidth (ArchReg PPC))
                  -> ArchSegmentOff PPC
                  -> MA.AbsBlockState (ArchReg PPC)
mkInitialAbsState = undefined

absEvalArchFn :: AbsProcessorState (ArchReg PPC) ids
              -> ArchFn PPC (Value PPC ids) tp
              -> AbsValue (RegAddrWidth (ArchReg PPC)) tp
absEvalArchFn = undefined

absEvalArchStmt :: AbsProcessorState (ArchReg PPC) ids
                -> ArchStmt PPC ids
                -> AbsProcessorState (ArchReg PPC) ids
absEvalArchStmt = undefined

postCallAbsState :: AbsBlockState (ArchReg PPC)
                 -> ArchSegmentOff PPC
                 -> AbsBlockState (ArchReg PPC)
postCallAbsState = undefined

identifyCall :: MM.Memory (ArchAddrWidth PPC)
             -> [Stmt PPC ids]
             -> RegState (ArchReg PPC) (Value PPC ids)
             -> Maybe (Seq.Seq (Stmt PPC ids), ArchSegmentOff PPC)
identifyCall = undefined

identifyReturn :: [Stmt PPC ids]
               -> RegState (ArchReg PPC) (Value PPC ids)
               -> Maybe [Stmt PPC ids]
identifyReturn = undefined

rewriteArchFn :: ArchFn PPC (Value PPC src) tp
              -> Rewriter PPC src tgt (Value PPC tgt tp)
rewriteArchFn = undefined

rewriteArchStmt :: ArchStmt PPC src
                -> Rewriter PPC src tgt ()
rewriteArchStmt = undefined

rewriteArchTermStmt :: ArchTermStmt PPC src
                    -> Rewriter PPC src tgt (ArchTermStmt PPC tgt)
rewriteArchTermStmt = undefined

archDemandContext :: MDS.DemandContext PPC ids
archDemandContext = undefined

-- | NOTE: There isn't necessarily one answer for this.  This will need to turn
-- into a function.  With PIC jump tables, it can be smaller than the native size.
jumpTableEntrySize :: MM.MemWord (ArchAddrWidth PPC)
jumpTableEntrySize = undefined

ppc_linux_info :: MI.ArchitectureInfo PPC
ppc_linux_info =
  MI.ArchitectureInfo { MI.withArchConstraints = undefined
                      , MI.archAddrWidth = undefined
                      , MI.archEndianness = MM.BigEndian
                      , MI.jumpTableEntrySize = jumpTableEntrySize
                      , MI.disassembleFn = disassembleFn
                      , MI.preserveRegAcrossSyscall = preserveRegAcrossSyscall
                      , MI.mkInitialAbsState = mkInitialAbsState
                      , MI.absEvalArchFn = absEvalArchFn
                      , MI.absEvalArchStmt = absEvalArchStmt
                      , MI.postCallAbsState = postCallAbsState
                      , MI.identifyCall = identifyCall
                      , MI.identifyReturn = identifyReturn
                      , MI.rewriteArchFn = rewriteArchFn
                      , MI.rewriteArchStmt = rewriteArchStmt
                      , MI.rewriteArchTermStmt = rewriteArchTermStmt
                      , MI.archDemandContext = archDemandContext
                      }
