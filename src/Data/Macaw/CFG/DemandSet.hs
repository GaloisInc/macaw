{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE RankNTypes #-}
module Data.Macaw.CFG.DemandSet
  ( DemandComp
  , DemandContext(..)
  , AssignIdSet
  , runDemandComp
  , addValueDemands
  , addStmtDemands
    -- * Filtering after demand set is computed.
  , stmtNeeded
  ) where

import           Control.Monad.State.Strict
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC
import           Data.Set (Set)
import qualified Data.Set as Set

import           Data.Macaw.CFG

------------------------------------------------------------------------
-- Functions for computing demanded values

type AssignIdSet ids = Set (Some (AssignId ids))

-- | This provides the architecture specific functions needed to
-- resolve demand sets.
data DemandContext arch ids
   = DemandContext { addArchStmtDemands :: !(ArchStmt arch ids  -> DemandComp arch ids ())
                   , addArchFnDemands   :: !(forall tp . ArchFn arch ids tp -> DemandComp arch ids ())
                   , archFnHasSideEffects :: !(forall tp . ArchFn arch ids tp -> Bool)
                     -- ^ This returns true if the architecture function has implicit
                     -- side effects (and thus can be safely removed).
                   }

-- | Return true if assign rhs has side effects (and thus should alwatys be demanded)
hasSideEffects :: DemandContext arch ids -> AssignRhs arch ids tp -> Bool
hasSideEffects ctx rhs =
  case rhs of
    EvalApp{} -> False
    SetUndefined{} -> False
    ReadMem{} -> True
    EvalArchFn fn _ -> archFnHasSideEffects ctx fn

data DemandState arch ids
   = DemandState { demandContext :: !(DemandContext arch ids)
                 , demandedAssignIds :: !(AssignIdSet ids)
                 }

-- | Monad used for computing demand sets.
newtype DemandComp arch ids a = DemandComp { unDemandComp :: State (DemandState arch ids) a }
  deriving (Functor, Applicative, Monad)

-- | Run demand computation and return the set of assignments that
-- were determined to be needed.
runDemandComp :: DemandContext arch ids -> DemandComp arch ids () -> AssignIdSet ids
runDemandComp ctx comp = demandedAssignIds $ execState (unDemandComp comp) s
  where s = DemandState { demandContext = ctx
                        , demandedAssignIds = Set.empty
                        }

-- | Record assign ids needed to compute this assignment right-hand
-- side.
addAssignRhsDemands :: AssignRhs arch ids tp -> DemandComp arch ids ()
addAssignRhsDemands rhs =
  case rhs of
    EvalApp app -> do
      traverseFC_ addValueDemands app
    SetUndefined{} ->
      pure ()
    ReadMem addr _ -> do
      addValueDemands addr
    EvalArchFn fn _ -> do
      ctx <- DemandComp $ gets $ demandContext
      addArchFnDemands ctx fn

-- | Add the ID of this assignment to demand set and also that of any
-- values needed to compute it.
addAssignmentDemands :: Assignment arch ids tp -> DemandComp arch ids ()
addAssignmentDemands a = do
  s <- DemandComp $ get
  let thisId = Some (assignId a)
  when (Set.notMember thisId (demandedAssignIds s)) $ do
    let s' = s { demandedAssignIds = Set.insert thisId (demandedAssignIds s) }
    seq s' $ DemandComp $ put s'
    addAssignRhsDemands (assignRhs a)

-- | Add any subassignments needed to compute values to demand set.
addValueDemands :: Value arch ids tp -> DemandComp arch ids ()
addValueDemands v = do
  case v of
    BVValue{} -> pure ()
    RelocatableValue{} -> pure ()
    AssignedValue a -> addAssignmentDemands a
    Initial{} ->  pure ()

-- | Parse statement, and if it has side effects, add assignments
-- needed to compute statement to demand set.
addStmtDemands :: Stmt arch ids -> DemandComp arch ids ()
addStmtDemands s =
  case s of
    AssignStmt a -> do
      ctx <- DemandComp $ gets demandContext
      when (hasSideEffects ctx (assignRhs a)) $ do
        addAssignmentDemands a
    WriteMem addr _repr val -> do
      addValueDemands addr
      addValueDemands val
    PlaceHolderStmt l _ ->
      mapM_ (\(Some v) -> addValueDemands v) l
    Comment _ ->
      pure ()
    ExecArchStmt astmt -> do
      ctx <- DemandComp $ gets $ demandContext
      addArchStmtDemands ctx astmt

------------------------------------------------------------------------
-- Functions for computing demanded values

-- | This returns true if the statement should be kept given the demand set.
stmtNeeded :: AssignIdSet ids -> Stmt arch ids -> Bool
stmtNeeded demandSet stmt =
  case stmt of
    AssignStmt a -> Set.member (Some (assignId a)) demandSet
    WriteMem{} -> True
    PlaceHolderStmt{} -> True
    Comment{} -> True
    ExecArchStmt{} -> True
