{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

-- | Functionality for resolving symbolic values to be concrete if possible.
-- This goes beyond @what4@ functions such as 'WI.asBV' by consulting an online
-- solver to see if the symbolic constraints on a value force is to be equal to
-- a single concrete value.
module Data.Macaw.Symbolic.Concretize
  ( resolveLLVMPtr
  , resolveSymBV
  , resolveSymNat
  ) where

import qualified Data.Parameterized.NatRepr as PN
import qualified Data.Traversable as T
import           GHC.TypeLits ( type (<=) )

import qualified Lang.Crucible.Backend as LCB
import qualified Lang.Crucible.Backend.Online as LCBO
import qualified Lang.Crucible.LLVM.MemModel as LCLM
import qualified What4.Expr as WE
import qualified What4.Expr.GroundEval as WEG
import qualified What4.Interface as WI
import qualified What4.Protocol.Online as WPO
import qualified What4.Protocol.SMTWriter as WPS
import qualified What4.SatResult as WSat
import qualified What4.Utils.BVDomain as WUB
import qualified What4.Utils.ResolveBounds.BV as WURB

-- | Resolve an 'LCLM.LLVMPtr' to be concrete if possible. The block ID and
-- offset are concretized independently, and either (or neither) could be
-- updated.
resolveLLVMPtr ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , 1 <= w
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> LCLM.LLVMPtr sym w
  -- ^ The symbolic pointer to concretize
  -> IO (LCLM.LLVMPtr sym w)
resolveLLVMPtr bak (LCLM.LLVMPointer base off) = do
  base' <- resolveSymNat bak base
  off' <- resolveSymBV bak (WI.bvWidth off) off
  pure (LCLM.LLVMPointer base' off')

-- | Resolve a 'WI.SymBV' to be concrete if possible. If the 'WI.SymBV' is truly
-- symbolic, this will try to constrain the lower and uppper bounds in the
-- abstract domain as much as possible.
resolveSymBV ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     , 1 <= w
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> PN.NatRepr w
  -- ^ The bitvector width
  -> WI.SymBV sym w
  -- ^ The symbolic bitvector to concretize
  -> IO (WI.SymBV sym w)
resolveSymBV bak w symBV =
  LCBO.withSolverProcess bak (onlinePanic "resolveSymBV") $ \sp -> do
    let sym = LCB.backendGetSym bak
    resBV <- WURB.resolveSymBV sym WURB.ExponentialSearch w sp symBV
    case resBV of
      WURB.BVConcrete bv ->
        WI.bvLit sym w bv
      WURB.BVSymbolic d -> do
        -- NB: Use annotateTerm here to ensure that subsequent What4
        -- simplifications do not rearrange the underlying expression, which
        -- could potentially widen the bounds. There is a chance that not
        -- simplifying the underlying expression could inhibit some potential
        -- optimizations, but we err on the side of having narrower bounds,
        -- which is generally more beneficial for the crucible-llvm memory
        -- model.
        (_, symBV') <- WI.annotateTerm sym $
                       WI.unsafeSetAbstractValue (WUB.BVDArith d) symBV
        pure symBV'

-- | Resolve a 'WI.SymNat' to be concrete if possible.
resolveSymNat ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     )
  => LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> WI.SymNat sym
  -- ^ The symbolic natural number to concretize
  -> IO (WI.SymNat sym)
resolveSymNat bak symNat = do
  let sym = LCB.backendGetSym bak
  symInt <- WI.natToInteger sym symNat
  resolvedSymInt <- resolveSymExpr concreteInteger bak symInt
  WI.integerToNat sym resolvedSymInt

-----
-- Internals
-----

-- | The scaffolding needed to concretize a 'WI.SymExpr' of a particular type.
-- This is a reasonable approach for concretizing most types, although there are
-- special cases where the concretization approach requires special care (see
-- 'resolveSymBV', for instance).
data Concretize sym tp where
  Concretize :: (WI.SymExpr sym tp -> Maybe (WEG.GroundValue tp))
                -- ^ Convert a symbolic term to a concrete value.
             -> (sym -> WEG.GroundValue tp -> IO (WI.SymExpr sym tp))
                -- ^ Inject a concrete value into a symbolic term.
             -> (sym -> WI.SymExpr sym tp -> WI.SymExpr sym tp -> IO (WI.Pred sym))
                -- ^ Check if two symbolic values are equal. This is used as
                -- part of creating a blocking clause when concretizing values
                -- with 'resolveSymExprOrFail'.
             -> Concretize sym tp

-- | 'Concretize' a symbolic integer.
concreteInteger :: (LCB.IsSymInterface sym) => Concretize sym WI.BaseIntegerType
concreteInteger = Concretize WI.asInteger WI.intLit WI.intEq

-- | Reasons why attempting to resolve a symbolic expression as concrete can
-- fail.
data ResolutionFailure
  = SolverUnknown
    -- ^ Querying the SMT solver yielded @UNKNOWN@.
  | UnsatInitialAssumptions
    -- ^ Querying the SMT solver for an initial model of the expression failed
    -- due to the initial assumptions in scope being unsatisfiable.
  | MultipleModels
    -- ^ There are multiple possible models for the expression, which means it
    -- is truly symbolic and therefore unable to be concretized.
  deriving Show

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using an
-- online SMT solver connection.
--
-- The implementation of this function asks for a model from the solver. If it
-- gets one, it adds a blocking clause and asks for another. If there was only
-- one model, concretize the initial value and return it with 'Right'.
-- Otherwise, return an explanation of why concretization failed with 'Left'.
resolveSymExprOrFail ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     )
  => Concretize sym tp
  -- ^ The strategy for concretizing the type
  -> LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> WI.SymExpr sym tp
  -- ^ The symbolic term to concretize
  -> IO (Either ResolutionFailure (WEG.GroundValue tp))
resolveSymExprOrFail (Concretize asConcrete injectSymbolic symEq) bak val =
  let sym = LCB.backendGetSym bak in
  case asConcrete val of
    Just val' -> pure $ Right val'
    Nothing -> do
      LCBO.withSolverProcess bak (onlinePanic "resolveSymExprAs") $ \sp -> do
        -- First, check to see if there is a model of the symbolic value.
        res <- WPO.inNewFrame sp $ do
          msat <- WPO.checkAndGetModel sp "Concretize value (with no assumptions)"
          mmodel <- case msat of
            WSat.Unknown -> pure $ Left SolverUnknown
            WSat.Unsat {} -> pure $ Left UnsatInitialAssumptions
            WSat.Sat mdl -> pure $ Right mdl
          T.forM mmodel $ \mdl -> WEG.groundEval mdl val
        case res of
          Left _failure -> pure res -- We failed to get a model
          Right concVal -> do
            -- We found a model, so check to see if this is the only possible
            -- model for this symbolic value.  We do this by adding a blocking
            -- clause that assumes the SymBV is /not/ equal to the model we
            -- found in the previous step. If this is unsatisfiable, the SymBV
            -- can only be equal to that model, so we can conclude it is
            -- concrete. If it is satisfiable, on the other hand, the SymBV can
            -- be multiple values, so it is truly symbolic.
            WPO.inNewFrame sp $ do
              injectedConcVal <- injectSymbolic sym concVal
              eq <- symEq sym val injectedConcVal
              block <- WI.notPred sym eq
              WPS.assume (WPO.solverConn sp) block
              msat <- WPO.checkAndGetModel sp "Concretize value (with blocking clause)"
              case msat of
                WSat.Unknown -> pure $ Left SolverUnknown -- Total failure
                WSat.Sat _mdl -> pure $ Left MultipleModels  -- There are multiple models
                WSat.Unsat {} -> pure res -- There is a single concrete result

-- | Attempt to resolve the given 'WI.SymExpr' to a concrete value using an
-- online SMT solver connection.
--
-- This is like 'resolveSymExprOrFail' except that this always returns a
-- 'WI.SymExpr'. In the event that concretization succeeds, the concrete value
-- will be injected into a symbolic value using the 'Concretize' argument. In
-- the event that concretization fails, this will simply return the original
-- symbolic value.
resolveSymExpr ::
     ( LCB.IsSymInterface sym
     , sym ~ WE.ExprBuilder scope st fs
     , WPO.OnlineSolver solver
     )
  => Concretize sym tp
  -- ^ The strategy for concretizing the type
  -> LCBO.OnlineBackend solver scope st fs
  -- ^ The symbolic backend
  -> WI.SymExpr sym tp
  -- ^ The symbolic term to concretize
  -> IO (WI.SymExpr sym tp)
resolveSymExpr concretize@(Concretize _ injectSymbolic _) bak val = do
  let sym = LCB.backendGetSym bak
  res <- resolveSymExprOrFail concretize bak val
  case res of
    Left _        -> pure val
    Right concVal -> injectSymbolic sym concVal

onlinePanic :: String -> a
onlinePanic fnName = error $ fnName ++ ": Online solver support is not enabled"
