{-|
Copyright  : (c) Galois, Inc 2017
Maintainer : jhendrix@galois.com

This applies constant propagations to transfor
-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Data.Macaw.Discovery.Opt
  ( -- * Basic types
    PropContext(..)
  , PropM
  , runPropM
  , propParsedBlock
    -- * Functions for defining architecture-specific semantics.
  , propValue
  ) where

import           Control.Lens
import           Control.Monad.State.Strict
import           Control.Monad.ST
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF

import           Data.Macaw.CFG
import           Data.Macaw.Discovery.State

-- | Information needed for propagation.
data PropContext arch src tgt
   = PropContext { propNonceGen  :: !(NonceGenerator (ST tgt) tgt)
                 , propArchStmt  :: !(ArchStmt arch src -> PropM arch src tgt ())
                 , propArchFn    :: !(forall tp . ArchFn arch src tp -> PropM arch src tgt (Value arch tgt tp))
                 }

-- | State used for
data PropState arch src tgt
   = PropState { propContext        :: !(PropContext arch src tgt)
               , _propRevStmts      :: ![Stmt arch tgt]
               , _srcAssignedValues :: !(MapF (AssignId src) (Value arch tgt))
               }

-- | A list of statements in the current block in reverse order.
propRevStmts :: Simple Lens (PropState arch src tgt) [Stmt arch tgt]
propRevStmts = lens _propRevStmts (\s v -> s { _propRevStmts = v })

-- | A list of statements in the current block in reverse order.
srcAssignedValues :: Simple Lens (PropState arch src tgt) (MapF (AssignId src) (Value arch tgt))
srcAssignedValues = lens _srcAssignedValues (\s v -> s { _srcAssignedValues = v })

-- | Monad for constant propagation within a block.
newtype PropM arch src tgt a = PropM { unPropM :: StateT (PropState arch src tgt) (ST tgt) a }
  deriving (Functor, Applicative, Monad)


runPropM :: PropContext arch src tgt
         -> PropM arch src tgt a
         -> ST tgt a
runPropM ctx m = evalStateT (unPropM m) s
  where s = PropState { propContext = ctx
                      , _propRevStmts = []
                      , _srcAssignedValues = MapF.empty
                      }

-- | Add a statment to the list
addStmt :: Stmt arch tgt -> PropM arch src tgt ()
addStmt stmt = PropM $ do
  stmts <- use propRevStmts
  let stmts' = stmt : stmts
  seq stmt $ seq stmts' $ do
  propRevStmts .= stmts'

-- | Add an assignment statement that evaluates the right hand side and return the resulting value.
evalAssignRhs :: AssignRhs arch tgt tp -> PropM arch src tgt (Value arch tgt tp)
evalAssignRhs rhs = PropM $ do
  gen <- gets $ propNonceGen . propContext
  aid <- lift $ AssignId <$> freshNonce gen
  let a = Assignment aid rhs
  unPropM $ addStmt $ AssignStmt a
  pure $! AssignedValue a

addBinding :: AssignId src tp -> Value arch tgt tp -> PropM arch src tgt ()
addBinding srcId val = PropM $ do
  srcAssignedValues %= MapF.insert srcId val

propApp :: App (Value arch tgt) tp -> PropM arch src tgt (Value arch tgt tp)
propApp app =
  case app of
    _ -> evalAssignRhs (EvalApp app)

propAssignRhs :: AssignRhs arch src tp -> PropM arch src tgt (Value arch tgt tp)
propAssignRhs rhs =
  case rhs of
    EvalApp app -> do
      app' <- traverseApp propValue app
      propApp app'
    SetUndefined w -> evalAssignRhs (SetUndefined w)
    ReadMem addr repr -> do
      tgtAddr <- propValue addr
      evalAssignRhs (ReadMem tgtAddr repr)
    EvalArchFn archFn _repr -> do
      f <- PropM $ gets $ propArchFn . propContext
      f archFn

propValue :: Value arch src tp -> PropM arch src tgt (Value arch tgt tp)
propValue v =
  case v of
    BVValue w i -> pure (BVValue w i)
    RelocatableValue w a -> pure (RelocatableValue w a)
    AssignedValue (Assignment aid _) -> do
      srcMap <- PropM $ use srcAssignedValues
      case MapF.lookup aid srcMap of
        Just tgtVal -> pure tgtVal
        Nothing -> fail $ "Could not resolve source assignment " ++ show aid ++ "."
    Initial r -> pure (Initial r)

-- | Apply optimizations to a statement.
--
-- Since statements may be introduced/deleted during optimization,
-- this should add new statements to the list of target statements
-- rather than return the optimized statement.
propStmt :: Stmt arch src -> PropM arch src tgt ()
propStmt s =
  case s of
    AssignStmt a -> do
      v <- propAssignRhs (assignRhs a)
      addBinding (assignId a) v
    WriteMem addr repr val -> do
      tgtAddr <- propValue addr
      tgtVal  <- propValue val
      addStmt (WriteMem tgtAddr repr tgtVal)
    PlaceHolderStmt args nm -> do
      args' <- traverse (traverseSome propValue) args
      addStmt (PlaceHolderStmt args' nm)
    Comment cmt -> addStmt (Comment cmt)
    ExecArchStmt astmt -> do
      f <- PropM $ gets $ propArchStmt . propContext
      f astmt

-- | Apply optimizations to a terminal statement.
propTermStmt :: ParsedTermStmt arch src -> PropM arch src tgt (ParsedTermStmt arch tgt)
propTermStmt tstmt = do
  case tstmt of
    ParsedCall regs mr -> do
      ParsedCall <$> traverseF propValue regs
                 <*> pure mr
    ParsedJump regs a -> do
      ParsedJump <$> traverseF propValue regs
                 <*> pure a
    ParsedLookupTable regs idx tbl -> do
      ParsedLookupTable <$> traverseF propValue regs
                        <*> propValue idx
                        <*> pure tbl
    ParsedReturn regs -> do
      ParsedReturn <$> traverseF propValue regs
    ParsedIte c t f ->
      ParsedIte <$> propValue c
                <*> propParsedBlock t
                <*> propParsedBlock f
    ParsedSyscall regs next ->
      ParsedSyscall <$> traverseF propValue regs
                    <*> pure next
    ParsedTranslateError txt -> pure (ParsedTranslateError txt)
    ClassifyFailure regs -> ClassifyFailure <$> traverseF propValue regs

-- | Apply optimizations to code in the block
propParsedBlock :: ParsedBlock arch src -> PropM arch src tgt (ParsedBlock arch tgt)
propParsedBlock b = do
  rstmts <- PropM $ use propRevStmts
  PropM $ propRevStmts .= []
  mapM_ propStmt (pblockStmts b)
  tgtTermStmt <- propTermStmt (pblockTerm b)
  -- Reset parent block stmts
  tgtStmts <- PropM $ use propRevStmts
  PropM $ propRevStmts .= rstmts
  -- Return new block
  pure $
    ParsedBlock { pblockLabel = pblockLabel b
                , pblockStmts = tgtStmts
                , pblockTerm  = tgtTermStmt
                }



{-
constPropRegion :: ParsedBlockRegion arch src
                -> ParsedBlockRegion arch tgt
constPropRegion r =
  r { regionBlockMap = constPropBlock <$> regionBlockMap r }
-}
