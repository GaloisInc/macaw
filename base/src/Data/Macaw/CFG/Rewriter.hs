{-|
Copyright  : (c) Galois, Inc 2017
Maintainer : jhendrix@galois.com

This provides a rewriter for simplifying values.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.CFG.Rewriter
  ( -- * Basic types
    RewriteContext(..)
  , Rewriter
  , runRewriter
  , rewriteStmt
  , rewriteValue
  , collectRewrittenStmts
  , evalRewrittenArchFn
  , appendRewrittenArchStmt
  ) where

import           Control.Lens
import           Control.Monad.State.Strict
import           Control.Monad.ST
import           Data.Bits
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableFC

import           Data.Macaw.CFG
import           Data.Macaw.Types

-- | Information needed for rewriting.
data RewriteContext arch src tgt
   = RewriteContext { rwctxNonceGen  :: !(NonceGenerator (ST tgt) tgt)
                      -- ^ Generator for making new nonces in the target ST monad
                    , rwctxArchFn    :: !(forall tp
                                            .  ArchFn arch (Value arch src) tp
                                            -> Rewriter arch src tgt (Value arch tgt tp))
                      -- ^ Rewriter for architecture-specific statements
                    , rwctxArchStmt  :: !(ArchStmt arch src -> Rewriter arch src tgt ())
                      -- ^ Rewriter for architecture-specific statements
                    , rwctxConstraints :: (forall a . (RegisterInfo (ArchReg arch) => a) -> a)
                      -- ^ Constraints needed during rewriting.
                    }

-- | State used by rewriter for tracking states
data RewriteState arch src tgt
   = RewriteState { -- | Access to the context for the rewriter
                    rwContext        :: !(RewriteContext arch src tgt)
                  , _rwRevStmts      :: ![Stmt arch tgt]
                  , _srcAssignedValues :: !(MapF (AssignId src) (Value arch tgt))
                  }

-- | A list of statements in the current block in reverse order.
rwRevStmts :: Simple Lens (RewriteState arch src tgt) [Stmt arch tgt]
rwRevStmts = lens _rwRevStmts (\s v -> s { _rwRevStmts = v })

-- | A map from source assignment identifiers to the updated value.
--
-- N.B. When using the rewriter, the user should process each statement sequentially so that every
-- assign id is mapped to a value.  If some of the assignments can be eliminated this should be
-- done via a dead code elimination step rather than during rewriting.
srcAssignedValues :: Simple Lens (RewriteState arch src tgt) (MapF (AssignId src) (Value arch tgt))
srcAssignedValues = lens _srcAssignedValues (\s v -> s { _srcAssignedValues = v })

-- | Monad for constant propagation within a block.
newtype Rewriter arch src tgt a = Rewriter { unRewriter :: StateT (RewriteState arch src tgt) (ST tgt) a }
  deriving (Functor, Applicative, Monad)

-- | Run the rewriter with the given conteext
runRewriter :: RewriteContext arch src tgt
            -> Rewriter arch src tgt a
            -> ST tgt a
runRewriter ctx m = evalStateT (unRewriter m) s
  where s = RewriteState { rwContext = ctx
                         , _rwRevStmts = []
                         , _srcAssignedValues = MapF.empty
                         }

-- | Add a statment to the list
appendRewrittenStmt :: Stmt arch tgt -> Rewriter arch src tgt ()
appendRewrittenStmt stmt = Rewriter $ do
  stmts <- use rwRevStmts
  let stmts' = stmt : stmts
  seq stmt $ seq stmts' $ do
  rwRevStmts .= stmts'

-- | Add a statment to the list
appendRewrittenArchStmt :: ArchStmt arch tgt -> Rewriter arch src tgt ()
appendRewrittenArchStmt = appendRewrittenStmt . ExecArchStmt

-- | Add an assignment statement that evaluates the right hand side and return the resulting value.
evalRewrittenRhs :: AssignRhs arch tgt tp -> Rewriter arch src tgt (Value arch tgt tp)
evalRewrittenRhs rhs = Rewriter $ do
  gen <- gets $ rwctxNonceGen . rwContext
  aid <- lift $ AssignId <$> freshNonce gen
  let a = Assignment aid rhs
  unRewriter $ appendRewrittenStmt $ AssignStmt a
  pure $! AssignedValue a

-- | Add an assignment statement that evaluates the architecture function.
evalRewrittenArchFn :: HasRepr (ArchFn arch (Value arch tgt)) TypeRepr
                    => ArchFn arch (Value arch tgt) tp
                    -> Rewriter arch src tgt (Value arch tgt tp)
evalRewrittenArchFn f = evalRewrittenRhs (EvalArchFn f (typeRepr f))

-- | Add a binding from the source assign id to the value.
addBinding :: AssignId src tp -> Value arch tgt tp -> Rewriter arch src tgt ()
addBinding srcId val = Rewriter $ do
  m <- use srcAssignedValues
  when (MapF.member srcId m) $ do
    fail $ "Assignment " ++ show srcId ++ " is already bound."
  srcAssignedValues .= MapF.insert srcId val m

-- | Return true if values are identical
identValue :: TestEquality (ArchReg arch) => Value arch tgt tp -> Value arch tgt tp -> Bool
identValue (BVValue _ x) (BVValue _ y) = x == y
identValue (RelocatableValue _ x) (RelocatableValue _ y) = x == y
identValue (AssignedValue x) (AssignedValue y) = assignId x == assignId y
identValue (Initial x) (Initial y) | Just Refl <- testEquality x y = True
identValue _ _ = False

boolLitValue :: Bool -> Value arch ids BoolType
boolLitValue = BoolValue

rewriteApp :: App (Value arch tgt) tp -> Rewriter arch src tgt (Value arch tgt tp)
rewriteApp app = do
  ctx <- Rewriter $ gets rwContext
  rwctxConstraints ctx $ do
  case app of
    Mux _ (BoolValue c) t f -> do
      if c then
        pure t
       else
        pure f

    Trunc (BVValue _ x) w -> do
      pure $ BVValue w $ toUnsigned w x
    SExt (BVValue u x) w -> do
      pure $ BVValue w $ toUnsigned w $ toSigned u x
    UExt (BVValue _ x) w -> do
      pure $ BVValue w x

    BoolMux (BoolValue b) x y -> do
      pure $! if b then x else y
    -- ite c T y = (~c | T) & (c | y)
    --           = c | y
    BoolMux c (BoolValue True) y -> do
      rewriteApp (OrApp c y)
    -- ite c F y = (~c | F) & (c | y)
    --           = ~c & y
    BoolMux c (BoolValue False) y -> do
      cn <- rewriteApp (NotApp c)
      rewriteApp (AndApp cn y)
    -- ite c x T = (~c | x) & (c | T)
    --           = ~c | x
    BoolMux c x (BoolValue True) -> do
      cn <- rewriteApp (NotApp c)
      rewriteApp (OrApp cn x)
    -- ite c x F = (~c | x) & (c | F)
    --           = c & x
    BoolMux c x (BoolValue False) -> do
      rewriteApp (AndApp c x)

    AndApp (BoolValue xc) y -> do
      if xc then
        pure y
       else
        pure (BoolValue False)
    AndApp x y@BoolValue{} -> rewriteApp (AndApp y x)

    OrApp (BoolValue xc) y -> do
      if xc then
        pure (BoolValue True)
       else
        pure y
    OrApp x y@BoolValue{} -> rewriteApp (OrApp y x)
    NotApp (BoolValue b) ->
      pure $! boolLitValue (not b)
    NotApp (valueAsApp -> Just (NotApp c)) ->
      pure $! c
    XorApp (BoolValue b) x ->
      if b then
        rewriteApp (NotApp x)
       else
        pure x
    XorApp x (BoolValue b) ->
      if b then
        rewriteApp (NotApp x)
       else
        pure x

    BVAdd _ x (BVValue _ 0) -> do
      pure x
    BVAdd w (BVValue _ x) (BVValue _ y) -> do
      pure (BVValue w (toUnsigned w (x + y)))
    -- Move constant to right
    BVAdd w (BVValue _ x) y -> do
      rewriteApp (BVAdd w y (BVValue w x))
    -- (x + yc) + zc -> x + (yc + zc)
    BVAdd w (valueAsApp -> Just (BVAdd _ x (BVValue _ yc))) (BVValue _ zc) -> do
      rewriteApp (BVAdd w x (BVValue w (toUnsigned w (yc + zc))))
    -- (x - yc) + zc -> x + (zc - yc)
    BVAdd w (valueAsApp -> Just (BVSub _ x (BVValue _ yc))) (BVValue _ zc) -> do
      rewriteApp (BVAdd w x (BVValue w (toUnsigned w (zc - yc))))
    -- (xc - y) + zc => (xc + zc) - y
    BVAdd w (valueAsApp -> Just (BVSub _ (BVValue _ xc) y)) (BVValue _ zc) -> do
      rewriteApp (BVSub w (BVValue w (toUnsigned w (xc + zc))) y)

    -- x - yc = x + (negate yc)
    BVSub w x (BVValue _ yc) -> do
      rewriteApp (BVAdd w x (BVValue w (toUnsigned w (negate yc))))

    -- x < y => x -> not (y <= x)
    BVUnsignedLt x y -> do
      r <- rewriteApp (BVUnsignedLe y x)
      rewriteApp (NotApp r)
    BVUnsignedLe (BVValue w x) (BVValue _ y) -> do
      pure $ boolLitValue $ toUnsigned w x <= toUnsigned w y

    -- x < y => x -> not (y <= x)
    BVSignedLt x y -> do
      r <- rewriteApp (BVSignedLe y x)
      rewriteApp (NotApp r)
    BVSignedLe (BVValue w x) (BVValue _ y) -> do

      pure $ boolLitValue $ toSigned w x <= toSigned w y
    BVTestBit (BVValue xw xc) (BVValue _ ic) | ic < min (natValue xw) (toInteger (maxBound :: Int))  -> do
      let v = xc `testBit` fromInteger ic
      pure $! boolLitValue v
    -- If we test the greatest bit turn this to a signed equality
    BVTestBit x (BVValue _ ic)
      | w <- typeWidth x
      , ic + 1 == natValue w -> do
      rewriteApp (BVSignedLt x (BVValue w 0))
    BVTestBit (valueAsApp -> Just (UExt x _)) i@(BVValue _ ic) -> do
      let xw = typeWidth x
      if ic < natValue xw then
        rewriteApp (BVTestBit x i)
       else
        pure (BoolValue False)
    BVTestBit (valueAsApp -> Just (BVAnd _ x y)) i@BVValue{} -> do
      xb <- rewriteApp (BVTestBit x i)
      yb <- rewriteApp (BVTestBit y i)
      rewriteApp (AndApp xb yb)
    BVTestBit (valueAsApp -> Just (BVOr _ x y)) i@BVValue{} -> do
      xb <- rewriteApp (BVTestBit x i)
      yb <- rewriteApp (BVTestBit y i)
      rewriteApp (OrApp xb yb)
    BVTestBit (valueAsApp -> Just (BVXor _ x y)) i -> do
      xb <- rewriteApp (BVTestBit x i)
      yb <- rewriteApp (BVTestBit y i)
      rewriteApp (XorApp xb yb)
    BVTestBit (valueAsApp -> Just (BVComplement _ x)) i -> do
      xb <- rewriteApp (BVTestBit x i)
      rewriteApp (NotApp xb)
    BVTestBit (valueAsApp -> Just (Mux _ c x y)) i -> do
      xb <- rewriteApp (BVTestBit x i)
      yb <- rewriteApp (BVTestBit y i)
      rewriteApp (BoolMux c xb yb)

    -- (x >> j) testBit i ~> x testBit (j+i)
    BVTestBit (valueAsApp -> Just (BVShr w x (BVValue _ j))) (BVValue _ i)
      | j + i < natValue w, j + i <= maxUnsigned w -> do
      rewriteApp (BVTestBit x (BVValue w (j + i)))

    BVComplement w (BVValue _ x) -> do
      pure (BVValue w (toUnsigned w (complement x)))

    BVAnd w (BVValue _ x) (BVValue _ y) -> do
      pure (BVValue w (x .&. y))
    -- Ensure constant with and is second argument.
    BVAnd w x@BVValue{} y -> do
      rewriteApp (BVAnd w y x)
    BVAnd _ _ y@(BVValue _ 0) -> do
      pure y
    BVAnd w x (BVValue _ yc) | yc == maxUnsigned w -> do
      pure x

    BVOr w (BVValue _ x) (BVValue _ y) -> do
      pure (BVValue w (x .|. y))
    BVOr w x@BVValue{} y -> do
      rewriteApp (BVOr w y x)
    BVOr _ x (BVValue _ 0) -> pure x
    BVOr w _ y@(BVValue _ yc) | yc == maxUnsigned w -> pure y

    BVXor w (BVValue _ x) (BVValue _ y) -> do
      pure (BVValue w (x `xor` y))
    BVXor w x@BVValue{} y -> rewriteApp (BVXor w y x)
    BVXor _ x (BVValue _ 0) -> pure x
    BVXor w x (BVValue _ yc) | yc == maxUnsigned w -> do
      rewriteApp (BVComplement w x)
    -- x `xor` y -> 0
    BVXor w x y | identValue x y -> do
      pure (BVValue w 0)


    BVShl w (BVValue _ x) (BVValue _ y) | y < toInteger (maxBound :: Int) -> do
      let s = min y (natValue w)
      pure (BVValue w (toUnsigned w (x `shiftL` fromInteger s)))
    BVShr w (BVValue _ x) (BVValue _ y) | y < toInteger (maxBound :: Int) -> do
      let s = min y (natValue w)
      pure (BVValue w (toUnsigned w (x `shiftR` fromInteger s)))
    BVSar w (BVValue _ x) (BVValue _ y) | y < toInteger (maxBound :: Int) -> do
      let s = min y (natValue w)
      pure (BVValue w (toUnsigned w (toSigned w x `shiftR` fromInteger s)))

    Eq (BoolValue x) (BoolValue y) -> do
      pure $! boolLitValue (x == y)

    Eq (BoolValue True) y -> do
      pure $! y
    Eq (BoolValue False) y -> do
      rewriteApp $ NotApp y

    Eq x (BoolValue True) -> do
      pure $! x
    Eq x (BoolValue False) -> do
      rewriteApp $ NotApp x

    Eq (BVValue _ x) (BVValue _ y) -> do
      pure $! boolLitValue (x == y)

    -- Move constant to right hand side.
    Eq x@BVValue{} y -> do
      rewriteApp (Eq y x)

    -- x + o = y ~> x = (y - o)
    Eq (valueAsApp -> Just (BVAdd w x (BVValue _ o))) (BVValue _ yc) -> do
      rewriteApp (Eq x (BVValue w (toUnsigned w (yc - o))))

    Eq (valueAsApp -> Just (BVSub _ x y)) (BVValue _ 0) -> do
      rewriteApp (Eq x y)

    Eq (valueAsApp -> Just (UExt x _)) (BVValue _ yc) -> do
      let u = typeWidth x
      if yc > maxUnsigned u then
        pure (BoolValue False)
       else
        rewriteApp (Eq x (BVValue u (toUnsigned u yc)))

    _ -> evalRewrittenRhs (EvalApp app)

rewriteAssignRhs :: AssignRhs arch src tp -> Rewriter arch src tgt (Value arch tgt tp)
rewriteAssignRhs rhs =
  case rhs of
    EvalApp app -> do
      rewriteApp =<< traverseFC rewriteValue app
    SetUndefined w -> evalRewrittenRhs (SetUndefined w)
    ReadMem addr repr -> do
      tgtAddr <- rewriteValue addr
      evalRewrittenRhs (ReadMem tgtAddr repr)
    EvalArchFn archFn _repr -> do
      f <- Rewriter $ gets $ rwctxArchFn . rwContext
      f archFn

rewriteValue :: Value arch src tp -> Rewriter arch src tgt (Value arch tgt tp)
rewriteValue v =
  case v of
    BoolValue b -> pure (BoolValue b)
    BVValue w i -> pure (BVValue w i)
    RelocatableValue w a -> pure (RelocatableValue w a)
    AssignedValue (Assignment aid _) -> do
      srcMap <- Rewriter $ use srcAssignedValues
      case MapF.lookup aid srcMap of
        Just tgtVal -> pure tgtVal
        Nothing -> fail $ "Could not resolve source assignment " ++ show aid ++ "."
    Initial r -> pure (Initial r)

-- | Apply optimizations to a statement.
--
-- Since statements may be introduced/deleted during optimization,
-- this should add new statements to the list of target statements
-- rather than return the optimized statement.
rewriteStmt :: Stmt arch src -> Rewriter arch src tgt ()
rewriteStmt s =
  case s of
    AssignStmt a -> do
      v <- rewriteAssignRhs (assignRhs a)
      addBinding (assignId a) v
    WriteMem addr repr val -> do
      tgtAddr <- rewriteValue addr
      tgtVal  <- rewriteValue val
      appendRewrittenStmt $ WriteMem tgtAddr repr tgtVal
    PlaceHolderStmt args nm -> do
      args' <- traverse (traverseSome rewriteValue) args
      appendRewrittenStmt $ PlaceHolderStmt args' nm
    Comment cmt ->
      appendRewrittenStmt $ Comment cmt
    InstructionStart off mnem ->
      appendRewrittenStmt $ InstructionStart off mnem
    ExecArchStmt astmt -> do
      f <- Rewriter $ gets $ rwctxArchStmt . rwContext
      f astmt

-- | This runs a rewrite action, and returns the statements generated while running it
-- along with the result of the action.
collectRewrittenStmts :: Rewriter arch src tgt a -> Rewriter arch src tgt ([Stmt arch tgt], a)
collectRewrittenStmts action = do
  rstmts <- Rewriter $ use rwRevStmts
  Rewriter $ rwRevStmts .= []
  r <- action
  tgtStmts <- Rewriter $ reverse <$> use rwRevStmts
  Rewriter $ rwRevStmts .= rstmts
  pure (tgtStmts, r)
