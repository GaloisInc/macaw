{-|
Copyright  : (c) Galois, Inc 2017-2019
Maintainer : jhendrix@galois.com

This provides a rewriter for simplifying blocks by rewriting value
computations and performing other rearrangement and adjustments.

The main entry point is calling 'runRewriter' with a constructed
'RewriteContext' to control the rewrite operation and a Rewriter monad
computation that rewrites the statements for a particular block.

Note that while the common case is a single block, the Branch TermStmt
that can be part of a block may refer to other Blocks (by ID) and
therefore the rewriting operation may need to actually modify multiple
blocks or even add new blocks for new Branch TermStmt targets.
-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.CFG.Rewriter
  ( -- * Basic types
    RewriteContext
  , mkRewriteContext
  , Rewriter
  , runRewriter
  , rewriteStmt
  , rewriteValue
  , rewriteApp
  , evalRewrittenArchFn
  , appendRewrittenArchStmt
  ) where

import           Control.Lens
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.BinarySymbols
import           Data.Bits
import           Data.List
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.TraversableFC
import           Data.STRef

import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Core
import           Data.Macaw.Memory
import           Data.Macaw.Types
import           Data.Macaw.CFG.Block (TermStmt)

-- | Information needed for rewriting.
data RewriteContext arch s src tgt
   = RewriteContext { rwctxNonceGen  :: !(NonceGenerator (ST s) tgt)
                      -- ^ Generator for making new nonces in the target ST monad
                    , rwctxArchFn
                      :: !(forall tp
                            .  ArchFn arch (Value arch src) tp
                            -> Rewriter arch s src tgt (Value arch tgt tp))
                      -- ^ Rewriter for architecture-specific functions
                    , rwctxArchStmt
                      :: !(ArchStmt arch (Value arch src) -> Rewriter arch s src tgt ())
                      -- ^ Rewriter for architecture-specific statements
                    , rwctxTermStmt
                      :: (TermStmt arch tgt ->
                          Rewriter arch s src tgt (TermStmt arch tgt))
                         -- ^ Rewriter for block terminal statements
                         -- for block at specified address to make any
                         -- additional adjustments beyond normal
                         -- discovery.
                    , rwctxConstraints
                      :: !(forall a . (RegisterInfo (ArchReg arch) => a) -> a)
                      -- ^ Constraints needed during rewriting.
                    , rwctxSectionAddrMap
                      :: !(Map SectionIndex (ArchSegmentOff arch))
                      -- ^ Map from section indices to the address they are loaded at
                      -- if any.
                      -- This is used to replace section references with their address.
                    , rwctxCache :: !(STRef s (MapF (AssignId src) (Value arch tgt)))
                      -- ^ A reference to a  map from source assignment
                      -- identifiers to the updated value.
                      --
                      -- N.B. When using the rewriter, the user should
                      -- process each statement sequentially so that
                      -- every assign id is mapped to a value.  If some
                      -- of the assignments can be eliminated this
                      -- should be done via a dead code elimination step
                      -- rather than during rewriting.
                    }

mkRewriteContext :: RegisterInfo (ArchReg arch)
                 => NonceGenerator (ST s) tgt
                 -> (forall tp
                     .  ArchFn arch (Value arch src) tp
                     -> Rewriter arch s src tgt (Value arch tgt tp))
                 -> (ArchStmt arch (Value arch src)
                     -> Rewriter arch s src tgt ())
                 -> (TermStmt arch tgt ->
                     Rewriter arch s src tgt (TermStmt arch tgt))
                    -- ^ Optional internal terminal statement
                    -- rewriter; e.g. use is for block jump targets
                    -- discovered outside normal pattern-matching in
                    -- Discovery.hs.
                 -> Map SectionIndex (ArchSegmentOff arch)
                    -- ^ Map from loaded section indices to their address.
                 -> ST s (RewriteContext arch s src tgt)
mkRewriteContext nonceGen archFn archStmt termStmt secAddrMap = do
  ref <- newSTRef MapF.empty
  pure $! RewriteContext { rwctxNonceGen = nonceGen
                         , rwctxArchFn = archFn
                         , rwctxArchStmt = archStmt
                         , rwctxTermStmt = termStmt
                         , rwctxConstraints = \a -> a
                         , rwctxSectionAddrMap = secAddrMap
                         , rwctxCache = ref
                         }

-- | State used by rewriter for tracking states
data RewriteState arch s src tgt
   = RewriteState { -- | Access to the context for the rewriter
                    rwContext        :: !(RewriteContext arch s src tgt)
                  , _rwRevStmts      :: ![Stmt arch tgt]
                  }

-- | A list of statements in the current block in reverse order.
rwRevStmts :: Simple Lens (RewriteState arch s src tgt) [Stmt arch tgt]
rwRevStmts = lens _rwRevStmts (\s v -> s { _rwRevStmts = v })

-- | Monad for constant propagation within a block.
newtype Rewriter arch s src tgt a = Rewriter { unRewriter :: StateT (RewriteState arch s src tgt) (ST s) a }
  deriving (Functor, Applicative, Monad)

-- | Run the rewriter with the given context
-- and collect the statements.
runRewriter :: RewriteContext arch s src tgt
            -> Rewriter arch s src tgt (TermStmt arch tgt)
            -> ST s ( RewriteContext arch s src tgt
                    , [Stmt arch tgt]
                    , (TermStmt arch tgt))
runRewriter ctx m = do
  let s = RewriteState { rwContext = ctx
                       , _rwRevStmts = []
                       }
      m' = rwctxTermStmt ctx =<< m
  (r, s') <- runStateT (unRewriter m') s
  pure (rwContext s', reverse (_rwRevStmts s'), r)

-- | Add a statement to the list
appendRewrittenStmt :: Stmt arch tgt -> Rewriter arch s src tgt ()
appendRewrittenStmt stmt = Rewriter $ do
  stmts <- use rwRevStmts
  let stmts' = stmt : stmts
  seq stmt $ seq stmts' $ do
    rwRevStmts .= stmts'

-- | Add a architecture-specific statement to the list
appendRewrittenArchStmt :: ArchStmt arch (Value arch tgt) -> Rewriter arch s src tgt ()
appendRewrittenArchStmt = appendRewrittenStmt . ExecArchStmt

-- | Add an assignment statement that evaluates the right hand side and return the resulting value.
evalRewrittenRhs :: AssignRhs arch (Value arch tgt) tp -> Rewriter arch s src tgt (Value arch tgt tp)
evalRewrittenRhs rhs = Rewriter $ do
  gen <- gets $ rwctxNonceGen . rwContext
  aid <- lift $ AssignId <$> freshNonce gen
  let a = Assignment aid rhs
  unRewriter $ appendRewrittenStmt $ AssignStmt a
  pure $! AssignedValue a

-- | Add an assignment statement that evaluates the architecture function.
evalRewrittenArchFn :: HasRepr (ArchFn arch (Value arch tgt)) TypeRepr
                    => ArchFn arch (Value arch tgt) tp
                    -> Rewriter arch s src tgt (Value arch tgt tp)
evalRewrittenArchFn f = evalRewrittenRhs (EvalArchFn f (typeRepr f))

-- | Add a binding from the source assign id to the value.
addBinding :: AssignId src tp -> Value arch tgt tp -> Rewriter arch s src tgt ()
addBinding srcId val = Rewriter $ do
  ref <- gets $ rwctxCache . rwContext
  lift $ do
    m <- readSTRef ref
    when (MapF.member srcId m) $ do
      fail $ "Assignment " ++ show srcId ++ " is already bound."
    writeSTRef ref $! MapF.insert srcId val m

-- | Return true if values are identical
identValue :: TestEquality (ArchReg arch) => Value arch tgt tp -> Value arch tgt tp -> Bool
identValue (BVValue _ x) (BVValue _ y) = x == y
identValue (RelocatableValue _ x) (RelocatableValue _ y) = x == y
identValue (AssignedValue x) (AssignedValue y) = assignId x == assignId y
identValue (Initial x) (Initial y) | Just Refl <- testEquality x y = True
identValue _ _ = False

boolLitValue :: Bool -> Value arch ids BoolType
boolLitValue = BoolValue

rewriteApp :: App (Value arch tgt) tp -> Rewriter arch s src tgt (Value arch tgt tp)
rewriteApp app = do
  ctx <- Rewriter $ gets rwContext
  rwctxConstraints ctx $ do
   case app of

    Trunc (BVValue _ x) w -> do
      pure $ BVValue w $ toUnsigned w x

    Trunc (valueAsApp -> Just (Mux _ c t@BVValue{} f@BVValue{})) w -> do
      t' <- rewriteApp (Trunc t w)
      f' <- rewriteApp (Trunc f w)
      rewriteApp $ Mux (BVTypeRepr w) c t' f'

    Trunc (valueAsApp -> Just (UExt v _)) w -> case compareNat w (typeWidth v) of
      NatLT _ -> rewriteApp $ Trunc v w
      NatEQ   -> pure v
      NatGT _ -> rewriteApp $ UExt v w
    Trunc (valueAsApp -> Just (SExt v _)) w -> case compareNat w (typeWidth v) of
      NatLT _ -> rewriteApp $ Trunc v w
      NatEQ   -> pure v
      NatGT _ -> rewriteApp $ SExt v w

    SExt (BVValue u x) w -> do
      pure $ BVValue w $ toUnsigned w $ toSigned u x
    UExt (BVValue _ x) w -> do
      pure $ BVValue w x

    Mux _ (BoolValue c) t f -> do
      pure $ if c then t else f
    Mux tp (valueAsApp -> Just (NotApp c)) t f -> do
      rewriteApp (Mux tp c f t)
    -- ite c T y = (~c | T) & (c | y)
    --           = c | y
    Mux _ c (BoolValue True) y -> do
      rewriteApp (OrApp c y)
    -- ite c F y = (~c | F) & (c | y)
    --           = ~c & y
    Mux BoolTypeRepr c (BoolValue False) y -> do
      cn <- rewriteApp (NotApp c)
      rewriteApp (AndApp cn y)
    -- ite c x T = (~c | x) & (c | T)
    --           = ~c | x
    Mux BoolTypeRepr c x (BoolValue True) -> do
      cn <- rewriteApp (NotApp c)
      rewriteApp (OrApp cn x)
    -- ite c x F = (~c | x) & (c | F)
    --           = c & x
    Mux BoolTypeRepr c x (BoolValue False) -> do
      rewriteApp (AndApp c x)

    AndApp (BoolValue xc) y -> do
      if xc then
        pure y
       else
        pure (BoolValue False)
    AndApp x y@BoolValue{} -> rewriteApp (AndApp y x)
    -- x < y && x <= y   =   x < y
    AndApp   (valueAsApp -> Just (BVUnsignedLe x  y ))
           v@(valueAsApp -> Just (BVUnsignedLt x' y'))
      | Just Refl <- testEquality (typeWidth x) (typeWidth x')
      , (x,y) == (x',y')
      -> pure v
    AndApp v@(valueAsApp -> Just (BVUnsignedLt x' y'))
             (valueAsApp -> Just (BVUnsignedLe x  y ))
      | Just Refl <- testEquality (typeWidth x) (typeWidth x')
      , (x,y) == (x',y')
      -> pure v
    AndApp   (valueAsApp -> Just (BVSignedLe x  y ))
           v@(valueAsApp -> Just (BVSignedLt x' y'))
      | Just Refl <- testEquality (typeWidth x) (typeWidth x')
      , (x,y) == (x',y')
      -> pure v
    AndApp v@(valueAsApp -> Just (BVSignedLt x' y'))
             (valueAsApp -> Just (BVSignedLe x  y ))
      | Just Refl <- testEquality (typeWidth x) (typeWidth x')
      , (x,y) == (x',y')
      -> pure v

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
    NotApp (valueAsApp -> Just (BVUnsignedLe x y)) ->
      rewriteApp (BVUnsignedLt y x)
    NotApp (valueAsApp -> Just (BVUnsignedLt x y)) ->
      rewriteApp (BVUnsignedLe y x)
    NotApp (valueAsApp -> Just (BVSignedLe x y)) ->
      rewriteApp (BVSignedLt y x)
    NotApp (valueAsApp -> Just (BVSignedLt x y)) ->
      rewriteApp (BVSignedLe y x)

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
    -- If first argument is constant and second is not, then commute.
    BVAdd w (BVValue _ x) y -> do
      rewriteApp $ BVAdd w y (BVValue w x)
    -- (x + yc) + zc -> x + (yc + zc)
    BVAdd w (valueAsApp -> Just (BVAdd _ x (BVValue _ yc))) (BVValue _ zc) -> do
      rewriteApp $ BVAdd w x (BVValue w (toUnsigned w (yc + zc)))
    -- (x - yc) + zc -> x + (zc - yc)
    BVAdd w (valueAsApp -> Just (BVSub _ x (BVValue _ yc))) (BVValue _ zc) -> do
      rewriteApp $ BVAdd w x (BVValue w (toUnsigned w (zc - yc)))
    -- (xc - y) + zc => (xc + zc) - y
    BVAdd w (valueAsApp -> Just (BVSub _ (BVValue _ xc) y)) (BVValue _ zc) -> do
      rewriteApp $ BVSub w (BVValue w (toUnsigned w (xc + zc))) y
    -- Increment address by a constant.
    BVAdd _ (RelocatableValue r a) (BVValue _ c) ->
      pure $ RelocatableValue r (incAddr c a)

    -- addr a + (c - addr b) => c + (addr a - addr b)
    BVAdd w (RelocatableValue _ a) (valueAsApp -> Just (BVSub _ c (RelocatableValue _ b)))
      | Just d <- diffAddr a b ->
        rewriteApp $ BVAdd w c (BVValue w (toUnsigned w d))

    -- x - yc = x + (negate yc)
    BVSub w x (BVValue _ yc) -> do
      rewriteApp (BVAdd w x (BVValue w (toUnsigned w (negate yc))))

    BVUnsignedLe (BVValue w x) (BVValue _ y) -> do
      pure $ boolLitValue $ toUnsigned w x <= toUnsigned w y
    BVUnsignedLe (BVValue w x) _ | toUnsigned w x == minUnsigned w -> do
      pure $ boolLitValue True
    BVUnsignedLe _ (BVValue w y) | toUnsigned w y == maxUnsigned w -> do
      pure $ boolLitValue True
    -- in uext(x) <= uext(y) we can eliminate one or both uext's.
    -- same for sext's, even with unsigned comparisons!
    -- uext(x) <= yc = true    if yc >= 2^width(x)-1
    -- uext(x) <= yc = x <= yc if yc <  2^width(x)-1
    -- similar shortcuts exist for the other inequalities
    BVUnsignedLe (BVValue _ x) (valueAsApp -> Just (UExt y _)) -> do
      let wShort = typeWidth y
      if x <= maxUnsigned wShort
        then rewriteApp (BVUnsignedLe (BVValue wShort x) y)
        else pure $ boolLitValue False
    BVUnsignedLe (valueAsApp -> Just (UExt x _)) (BVValue _ y) -> do
      let wShort = typeWidth x
      if y < maxUnsigned wShort
        then rewriteApp (BVUnsignedLe x (BVValue wShort y))
        else pure $ boolLitValue True
    BVUnsignedLe (valueAsApp -> Just (UExt x _)) (valueAsApp -> Just (UExt y _)) -> do
      let wx = typeWidth x
          wy = typeWidth y
      case compareNat wx wy of
        NatLT _ -> rewriteApp (UExt x wy) >>= \x' -> rewriteApp (BVUnsignedLe x' y)
        NatEQ   -> rewriteApp (BVUnsignedLe x y)
        NatGT _ -> rewriteApp (UExt y wx) >>= \y' -> rewriteApp (BVUnsignedLe x y')
    BVUnsignedLe (valueAsApp -> Just (SExt x _)) (valueAsApp -> Just (SExt y _)) -> do
      let wx = typeWidth x
          wy = typeWidth y
      case compareNat wx wy of
        NatLT _ -> rewriteApp (SExt x wy) >>= \x' -> rewriteApp (BVUnsignedLe x' y)
        NatEQ   -> rewriteApp (BVUnsignedLe x y)
        NatGT _ -> rewriteApp (SExt y wx) >>= \y' -> rewriteApp (BVUnsignedLe x y')

    BVUnsignedLt (BVValue w x) (BVValue _ y) -> do
      pure $ boolLitValue $ toUnsigned w x < toUnsigned w y
    BVUnsignedLt (BVValue w x) _ | toUnsigned w x == maxUnsigned w -> do
      pure $ boolLitValue False
    BVUnsignedLt _ (BVValue w x) | toUnsigned w x == minUnsigned w -> do
      pure $ boolLitValue False
    BVUnsignedLt (BVValue _ x) (valueAsApp -> Just (UExt y _)) -> do
      let wShort = typeWidth y
      if x < maxUnsigned wShort
        then rewriteApp (BVUnsignedLt (BVValue wShort x) y)
        else pure $ boolLitValue False
    BVUnsignedLt (valueAsApp -> Just (UExt x _)) (BVValue _ y) -> do
      let wShort = typeWidth x
      if y <= maxUnsigned wShort
        then rewriteApp (BVUnsignedLt x (BVValue wShort y))
        else pure $ boolLitValue True
    BVUnsignedLt (valueAsApp -> Just (UExt x _)) (valueAsApp -> Just (UExt y _)) -> do
      let wx = typeWidth x
          wy = typeWidth y
      case compareNat wx wy of
        NatLT _ -> rewriteApp (UExt x wy) >>= \x' -> rewriteApp (BVUnsignedLt x' y)
        NatEQ   -> rewriteApp (BVUnsignedLt x y)
        NatGT _ -> rewriteApp (UExt y wx) >>= \y' -> rewriteApp (BVUnsignedLt x y')
    BVUnsignedLt (valueAsApp -> Just (SExt x _)) (valueAsApp -> Just (SExt y _)) -> do
      let wx = typeWidth x
          wy = typeWidth y
      case compareNat wx wy of
        NatLT _ -> rewriteApp (SExt x wy) >>= \x' -> rewriteApp (BVUnsignedLt x' y)
        NatEQ   -> rewriteApp (BVUnsignedLt x y)
        NatGT _ -> rewriteApp (SExt y wx) >>= \y' -> rewriteApp (BVUnsignedLt x y')

    BVSignedLe (BVValue w x) (BVValue _ y) -> do
      pure $ boolLitValue $ toSigned w x <= toSigned w y
    BVSignedLe (BVValue w x) _ | toSigned w x == minSigned w -> do
      pure $ boolLitValue True
    BVSignedLe _ (BVValue w y) | toSigned w y == maxSigned w -> do
      pure $ boolLitValue True
    BVSignedLe (BVValue w x) (valueAsApp -> Just (SExt y _)) -> do
      let wShort = typeWidth y
          xv = toSigned w x
      if xv <= minSigned wShort
        then pure $ boolLitValue True
        else if xv > maxSigned wShort
          then pure $ boolLitValue False
          else rewriteApp (BVSignedLe (BVValue wShort x) y)
    BVSignedLe (valueAsApp -> Just (SExt x _)) (BVValue w y) -> do
      let wShort = typeWidth x
          yv = toSigned w y
      if yv < minSigned wShort
        then pure $ boolLitValue False
        else if yv >= maxSigned wShort
          then pure $ boolLitValue True
          else rewriteApp (BVSignedLe x (BVValue wShort y))
    BVSignedLe (valueAsApp -> Just (SExt x _)) (valueAsApp -> Just (SExt y _)) -> do
      let wx = typeWidth x
          wy = typeWidth y
      case compareNat wx wy of
        NatLT _ -> rewriteApp (SExt x wy) >>= \x' -> rewriteApp (BVUnsignedLe x' y)
        NatEQ   -> rewriteApp (BVUnsignedLe x y)
        NatGT _ -> rewriteApp (SExt y wx) >>= \y' -> rewriteApp (BVUnsignedLe x y')
    -- for signed comparisons, uext(x) <= uext(y) is not necessarily equivalent
    -- to either x <= uext(y) or uext(x) <= y, so no rewrite for that!

    BVSignedLt (BVValue w x) (BVValue _ y) -> do
      pure $ boolLitValue $ toSigned w x < toSigned w y
    BVSignedLt (BVValue w x) _ | toSigned w x == maxSigned w -> do
      pure $ boolLitValue False
    BVSignedLt _ (BVValue w y) | toSigned w y == minSigned w -> do
      pure $ boolLitValue False
    BVSignedLt (BVValue w x) (valueAsApp -> Just (SExt y _)) -> do
      let wShort = typeWidth y
          xv = toSigned w x
      if xv < minSigned wShort
        then pure $ boolLitValue True
        else if xv >= maxSigned wShort
          then pure $ boolLitValue False
          else rewriteApp (BVSignedLt (BVValue wShort x) y)
    BVSignedLt (valueAsApp -> Just (SExt x _)) (BVValue w y) -> do
      let wShort = typeWidth x
          yv = toSigned w y
      if yv <= minSigned wShort
        then pure $ boolLitValue False
        else if yv > maxSigned wShort
          then pure $ boolLitValue True
          else rewriteApp (BVSignedLt x (BVValue wShort y))
    BVSignedLt (valueAsApp -> Just (SExt x _)) (valueAsApp -> Just (SExt y _)) -> do
      let wx = typeWidth x
          wy = typeWidth y
      case compareNat wx wy of
        NatLT _ -> rewriteApp (SExt x wy) >>= \x' -> rewriteApp (BVUnsignedLt x' y)
        NatEQ   -> rewriteApp (BVUnsignedLt x y)
        NatGT _ -> rewriteApp (SExt y wx) >>= \y' -> rewriteApp (BVUnsignedLt x y')

    BVTestBit (BVValue xw xc) (BVValue _ ic) | ic < min (intValue xw) (toInteger (maxBound :: Int))  -> do
      let v = xc `testBit` fromInteger ic
      pure $! boolLitValue v
    -- If we test the greatest bit turn this to a signed equality
    BVTestBit x (BVValue _ ic)
      | w <- typeWidth x
      , ic + 1 == intValue w -> do
      rewriteApp (BVSignedLt x (BVValue w 0))
      | w <- typeWidth x
      , ic >= intValue w -> pure (boolLitValue False)
    BVTestBit (valueAsApp -> Just (UExt x _)) (BVValue _ ic) -> do
      let xw = typeWidth x
      if ic < intValue xw then
        rewriteApp (BVTestBit x (BVValue xw ic))
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
      rewriteApp (Mux BoolTypeRepr c xb yb)

    -- (x >> j) testBit i ~> x testBit (i+j)
    -- (x << j) testBit i ~> x testBit (i-j)
    -- plus a couple special cases for when the tested bit falls outside the shifted value
    BVTestBit (valueAsApp -> Just (BVShr w x (BVValue _ j))) (BVValue _ i)
      | j + i <= maxUnsigned w -> do
      rewriteApp (BVTestBit x (BVValue w (j + i)))
    BVTestBit (valueAsApp -> Just (BVSar w x (BVValue _ j))) (BVValue _ i)
      | i < intValue w -> do
      rewriteApp (BVTestBit x (BVValue w (min (j + i) (intValue w-1))))
    BVTestBit (valueAsApp -> Just (BVShl w x (BVValue _ j))) (BVValue _ i)
      | j <= i -> rewriteApp (BVTestBit x (BVValue w (i - j)))
      | otherwise -> pure (boolLitValue False)

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
    BVAnd _ x y | x == y -> pure x

    BVOr w (BVValue _ x) (BVValue _ y) -> do
      pure (BVValue w (x .|. y))
    BVOr w x@BVValue{} y -> do
      rewriteApp (BVOr w y x)
    BVOr _ x (BVValue _ 0) -> pure x
    BVOr w _ y@(BVValue _ yc) | yc == maxUnsigned w -> pure y
    BVOr _ x y | x == y -> pure x

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
      let s = min y (intValue w)
      pure (BVValue w (toUnsigned w (x `shiftL` fromInteger s)))
    BVShr w (BVValue _ x) (BVValue _ y) | y < toInteger (maxBound :: Int) -> do
      let s = min y (intValue w)
      pure (BVValue w (toUnsigned w (x `shiftR` fromInteger s)))
    BVSar w (BVValue _ x) (BVValue _ y) | y < toInteger (maxBound :: Int) -> do
      let s = min y (intValue w)
      pure (BVValue w (toUnsigned w (toSigned w x `shiftR` fromInteger s)))

    BVShl _ v (BVValue _ 0) -> pure v
    BVShr _ v (BVValue _ 0) -> pure v
    BVSar _ v (BVValue _ 0) -> pure v

    BVShl w _ (BVValue _ n) | n >= intValue w ->
      pure (BVValue w 0)
    BVShr w _ (BVValue _ n) | n >= intValue w ->
      pure (BVValue w 0)

    PopCount w (BVValue _ x) -> do
      pure $ BVValue w $ fromIntegral $ popCount $ toUnsigned w x
    Bsr w (BVValue _ x) -> do
      let i = fromJust $ find
                (\j -> toUnsigned w x `shiftR` fromIntegral j == 0)
                [0 .. intValue w]
      pure $ BVValue w $ intValue w - i

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

    Eq (valueAsApp -> Just (Mux _ c t@BVValue{} f@BVValue{})) z@BVValue{} -> do
      t' <- rewriteApp (Eq t z)
      f' <- rewriteApp (Eq f z)
      rewriteApp $ Mux BoolTypeRepr c t' f'

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

    -- no normal rewrites available, now try mhnf for enabling Discovery
    _ -> rewriteMhnf app


-- | Performs rewrites for "Mux Head Normal Form", which attempts to
-- raise Mux operations upwards to make them more likely to appear as
-- the last statement in a Block.  This is needed because
-- parseFetchAndExecute in Discovery will attempt to recognize branch
-- statements by pattern matching the value of the IP register as a
-- Mux.
--
-- For example, the following:
--
--     r32 := Mux r31 (0x4 :: [64]) (0x28 :: [64])
--     r33 := Add r32 (0x100a3e50)
--     { ip => r33, ... }
--
-- should be rewritten to:
--
--     r34 := Mux r31 (0x100a3e54) (0x100a3e78)
--     { ip => r34, ... }
--
-- so that the Mux itself is the ip register's valueAsApp.  (Note that
-- the BVAdd of the two r32 branch values and the r33 second argument
-- are reduced to simple values by the rewriter here as well.
--
-- This rewrite is performed after other rewrites to increase the
-- chances of it raising the Mux past previously rewrite-simplified
-- statements, although it still recurses into the main rewriter.
rewriteMhnf :: App (Value arch tgt) tp -> Rewriter arch s src tgt (Value arch tgt tp)
rewriteMhnf app = do
  ctx <- Rewriter $ gets rwContext
  rwctxConstraints ctx $ do
   case app of

     BVAdd w (valueAsApp -> Just (Mux p c t f)) v@(BVValue _ _) -> do
       t' <- rewriteApp (BVAdd w t v)
       f' <- rewriteApp (BVAdd w f v)
       rewriteApp $ Mux p c t' f'

     BVAdd w (valueAsApp -> Just (Mux p c t f)) v@(RelocatableValue _ _) -> do
       t' <- rewriteApp (BVAdd w t v)
       f' <- rewriteApp (BVAdd w f v)
       rewriteApp $ Mux p c t' f'

     -- no more rewrites applicable, so return the final result
     _ -> evalRewrittenRhs (EvalApp app)


rewriteAssignRhs :: AssignRhs arch (Value arch src) tp
                 -> Rewriter arch s src tgt (Value arch tgt tp)
rewriteAssignRhs rhs =
  case rhs of
    EvalApp app -> do
      rewriteApp =<< traverseFC rewriteValue app
    SetUndefined w -> evalRewrittenRhs (SetUndefined w)
    ReadMem addr repr -> do
      tgtAddr <- rewriteValue addr
      evalRewrittenRhs (ReadMem tgtAddr repr)
    CondReadMem repr cond0 addr0 def0 -> do
      cond <- rewriteValue cond0
      addr <- rewriteValue addr0
      case () of
        _ | BoolValue b <- cond ->
            if b then
              evalRewrittenRhs (ReadMem addr repr)
             else
              rewriteValue def0
        _ -> do
          def  <- rewriteValue def0
          evalRewrittenRhs (CondReadMem repr cond addr def)
    EvalArchFn archFn _repr -> do
      f <- Rewriter $ gets $ rwctxArchFn . rwContext
      f archFn

rewriteValue :: Value arch src tp -> Rewriter arch s src tgt (Value arch tgt tp)
rewriteValue v =
  case v of
    BoolValue b -> pure (BoolValue b)
    BVValue w i -> pure (BVValue w i)
    RelocatableValue w a -> pure (RelocatableValue w a)
    SymbolValue repr sym -> do
      ctx <- Rewriter $ gets rwContext
      rwctxConstraints ctx $ do
        let secIdxAddrMap = rwctxSectionAddrMap ctx
        case sym of
          SectionIdentifier secIdx
            | Just val <- Map.lookup secIdx secIdxAddrMap -> do
                pure $! RelocatableValue repr (segoffAddr val)
          _ -> do
            pure $! SymbolValue repr sym
    AssignedValue (Assignment aid _) -> Rewriter $ do
      ref <- gets $ rwctxCache . rwContext
      srcMap <- lift $ readSTRef ref
      case MapF.lookup aid srcMap of
        Just tgtVal -> pure tgtVal
        Nothing -> fail $ "Could not resolve source assignment " ++ show aid ++ "."
    Initial r -> pure (Initial r)

-- | Apply optimizations to a statement.
--
-- Since statements may be introduced/deleted during optimization,
-- this should add new statements to the list of target statements
-- rather than return the optimized statement.
rewriteStmt :: Stmt arch src -> Rewriter arch s src tgt ()
rewriteStmt s =
  case s of
    AssignStmt a -> do
      v <- rewriteAssignRhs (assignRhs a)
      addBinding (assignId a) v
    WriteMem addr repr val -> do
      tgtAddr <- rewriteValue addr
      tgtVal  <- rewriteValue val
      appendRewrittenStmt $ WriteMem tgtAddr repr tgtVal
    CondWriteMem cond addr repr val -> do
      tgtCond <- rewriteValue cond
      tgtAddr <- rewriteValue addr
      tgtVal  <- rewriteValue val
      appendRewrittenStmt $ CondWriteMem tgtCond tgtAddr repr tgtVal
    Comment cmt ->
      appendRewrittenStmt $ Comment cmt
    InstructionStart off mnem ->
      appendRewrittenStmt $ InstructionStart off mnem
    ExecArchStmt astmt -> do
      f <- Rewriter $ gets $ rwctxArchStmt . rwContext
      f astmt
    ArchState addr updates -> do
      tgtUpdates <- MapF.traverseWithKey (const rewriteValue) updates
      appendRewrittenStmt $ ArchState addr tgtUpdates
