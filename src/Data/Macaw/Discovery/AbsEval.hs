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
  , assignmentAbsValues
  ) where

import           Control.Lens
import           Control.Monad.State.Strict
import           Data.Foldable
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import qualified Data.Set as Set

import           Data.Macaw.AbsDomain.AbsState
import           Data.Macaw.Architecture.Info
import           Data.Macaw.CFG

import           Data.Macaw.Memory

-- | Get the absolute value associated with an address.
absEvalReadMem :: (OrdF (ArchReg a), ShowF (ArchReg a), MemWidth (RegAddrWidth (ArchReg a)))
                => AbsProcessorState (ArchReg a) ids
                -> ArchAddrValue a ids
                -> MemRepr tp
                   -- ^ Information about the memory layout for the value.
                -> ArchAbsValue a tp
absEvalReadMem r a tp
  | StackOffset _ s <- transferValue r a
  , [o] <- Set.toList s
  , Just (StackEntry v_tp v) <- Map.lookup o (r^.curAbsStack)
  , Just Refl <- testEquality tp v_tp = v
  | otherwise = TopV

-- | Get the abstract domain for the right-hand side of an assignment.
transferRHS :: ArchitectureInfo a
            -> AbsProcessorState (ArchReg a) ids
            -> AssignRhs a ids tp
            -> ArchAbsValue a tp
transferRHS info r rhs =
  case rhs of
    EvalApp app    -> withArchConstraints info $ transferApp r app
    SetUndefined _ -> TopV
    ReadMem a tp   -> withArchConstraints info $ absEvalReadMem r a tp
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
    PlaceHolderStmt{} ->
      pure ()
    Comment{} ->
      pure ()
    ExecArchStmt astmt ->
      modify $ \r -> absEvalArchStmt info r astmt

absEvalStmts :: ArchitectureInfo arch
              -> AbsProcessorState (ArchReg arch) ids
              -> [Stmt arch ids]
              -> AbsProcessorState (ArchReg arch) ids
absEvalStmts info r stmts = execState (mapM_ (absEvalStmt info) stmts) r

-- | Generate map that maps each assignment in the CFG to the abstract value
-- associated with it.
assignmentAbsValues :: forall arch ids
                    .  ArchitectureInfo arch
                    -> Memory (ArchAddrWidth arch)
                    -> CFG arch ids
                    -> Map (ArchSegmentedAddr arch) (AbsBlockState (ArchReg arch))
                       -- ^ Maps addresses to the initial state at that address.
                    -> MapF (AssignId ids) (ArchAbsValue arch)
assignmentAbsValues info mem g absm =
     foldl' go MapF.empty (Map.elems (g^.cfgBlocks))
  where go :: MapF (AssignId ids) (ArchAbsValue arch)
           -> Block arch ids
           -> MapF (AssignId ids) (ArchAbsValue arch)
        go m0 b =
          case blockLabel b of
            GeneratedBlock a 0 -> do
              case Map.lookup a absm of
                Nothing -> do
                  error $ "internal: assignmentAbsValues could not find code infomation for block " ++ show a
                Just blockState -> do
                  let abs_state = initAbsProcessorState mem blockState
                  insBlock b abs_state m0
            _ -> m0

        insBlock :: Block arch ids
                 -> AbsProcessorState (ArchReg arch) ids
                 -> MapF (AssignId ids) (ArchAbsValue arch)
                 -> MapF (AssignId ids) (ArchAbsValue arch)
        insBlock b r0 m0 =
          let final = absEvalStmts info r0 (blockStmts b)
              m = MapF.union (final^.absAssignments) m0 in
          case blockTerm b of
            Branch _ lb rb -> do
              let Just l = findBlock g lb
              let Just r = findBlock g rb
              insBlock l final $
                insBlock r final $
                m
            FetchAndExecute _ -> m
            Syscall _ -> m
            TranslateError{} -> m
