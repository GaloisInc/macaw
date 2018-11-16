{- |
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>, Simon Winwood <sjw@galois.com>

This provides a set of functions for abstract evaluation of statements.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Macaw.Discovery.AbsEval
  ( absEvalStmts
  , absEvalReadMem
  ) where

import           Control.Lens
import           Control.Monad.State.Strict
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import qualified Data.Set as Set

import           Data.Macaw.AbsDomain.AbsState
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG

-- | Get the abstract value associated with an address.
absEvalReadMem :: RegisterInfo (ArchReg a)
               => AbsProcessorState (ArchReg a) ids
               -> ArchAddrValue a ids
               -> MemRepr tp
                  -- ^ Information about the memory layout for the value.
               -> ArchAbsValue a tp
absEvalReadMem r a tp
    -- If the value is a stack entry, then see if there is a stack
    -- value associated with it.
  | StackOffset _ s <- transferValue r a
  , [o] <- Set.toList s
  , Just (StackEntry v_tp v) <- Map.lookup o (r^.curAbsStack)
  , Just Refl <- testEquality tp v_tp = v
  | otherwise = TopV

-- | Get the abstract domain for the right-hand side of an assignment.
transferRHS :: ArchitectureInfo a
            -> AbsProcessorState (ArchReg a) ids
            -> AssignRhs a (Value a ids) tp
            -> ArchAbsValue a tp
transferRHS info r rhs =
  case rhs of
    EvalApp app    -> withArchConstraints info $ transferApp r app
    SetUndefined _ -> TopV
    ReadMem a tp   -> withArchConstraints info $ absEvalReadMem r a tp

    -- TODO: See if we should build a mux specific version
    CondReadMem tp _ a d ->
      withArchConstraints info $ do
        lub (absEvalReadMem r a tp)
            (transferValue r d)
    EvalArchFn f _ -> absEvalArchFn info r f

-- | Merge in the value of the assignment.
--
-- If we have already seen a value, this will combine with meet.
addAssignment :: ArchitectureInfo a
              -> Assignment a ids tp
              -> AbsProcessorState (ArchReg a) ids
              -> AbsProcessorState (ArchReg a) ids
addAssignment info a c = withArchConstraints info $
  c & (absAssignments . assignLens (assignId a))
    %~ (`meet` transferRHS info c (assignRhs a))

-- | Given a statement this modifies the processor state based on the statement.
absEvalStmt :: ArchitectureInfo arch
             -> Stmt arch ids
             -> State (AbsProcessorState (ArchReg arch) ids) ()
absEvalStmt info stmt = withArchConstraints info $
  case stmt of
    AssignStmt a ->
      modify $ addAssignment info a
    WriteMem addr memRepr v ->
      modify $ addMemWrite addr memRepr v
    InstructionStart _ _ ->
      pure ()
    Comment{} ->
      pure ()
    ExecArchStmt astmt ->
      modify $ \r -> absEvalArchStmt info r astmt
    ArchState{} ->
      pure ()

-- This takes a processor state and updates it based on executing each statement.
absEvalStmts :: Foldable t
             => ArchitectureInfo arch
             -> AbsProcessorState (ArchReg arch) ids
             -> t (Stmt arch ids)
             -> AbsProcessorState (ArchReg arch) ids
absEvalStmts info r stmts = execState (mapM_ (absEvalStmt info) stmts) r
