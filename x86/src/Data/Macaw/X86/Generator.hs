{-
Copyright        : (c) Galois, Inc 2015-2017
Maintainer       : Joe Hendrix <jhendrix@galois.com>, Simon Winwood <sjw@galois.com>

This defines the monad @X86Generator@, which provides operations for
modeling X86 semantics.
-}
{-# LANGUAGE CPP #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE ViewPatterns #-}
module Data.Macaw.X86.Generator
  ( -- * X86Generator
    X86Generator(..)
  , runX86Generator
  , X86GCont
  , addAssignment
  , addStmt
  , addTermStmt
  , addArchStmt
  , addArchTermStmt
  , asAtomicStateUpdate
  , evalArchFn
  , evalAssignRhs
  , getState
    -- * PartialBlock
  , PartialBlock
  , unfinishedAtAddr
  , finishPartialBlock
    -- * PreBlock
  , PreBlock
  , emptyPreBlock
  , pBlockState
  , pBlockStmts
  , pBlockApps
  , pBlockStart
    -- * GenState
  , GenState(..)
  , blockState
  , curX86State
    -- * Expr
  , Expr(..)
  , app
  , asApp
  , asArchFn
  , asBoolLit
  , asUnsignedBVLit
  , asSignedBVLit
  , eval
  , getRegValue
  , setReg
  , incAddr
    -- * AVX mode
  , isAVX
  , inAVX
  ) where

import           Control.Lens
import           Control.Monad.Cont
import           Control.Monad.Except
#if __GLASGOW_HASKELL__ < 808
import           Control.Monad.Fail
#endif
import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State.Strict
import           Data.Bits
import           Data.Foldable
import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Block
import           Data.Macaw.CFG.Core
import           Data.Macaw.Memory
import           Data.Macaw.Types
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.TraversableFC
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import           Data.Text (Text)
import qualified Data.Text as Text
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import           Data.Macaw.X86.ArchTypes
import           Data.Macaw.X86.X86Reg

------------------------------------------------------------------------
-- Expr

-- | A pure expression for isValue.
data Expr ids tp where
  -- | An expression obtained from some value.
  ValueExpr :: !(Value X86_64 ids tp) -> Expr ids tp
  -- | An expression that is computed from evaluating subexpressions.
  AppExpr :: !(App (Expr ids) tp) -> Expr ids tp

collectExpr :: Expr ids tp -> State (MapF (AssignId ids) DocF) PP.Doc
collectExpr (ValueExpr v) = collectValueRep 0 v
collectExpr (AppExpr a) = ppAppA collectExpr a

instance PP.Pretty (Expr ids tp) where
  pretty e = ppValueAssignments' (collectExpr e)

instance Show (Expr ids tp) where
  show (ValueExpr v) = show v
  show AppExpr{} = "app"

instance ShowF (Expr ids)

instance Eq (Expr ids tp) where
  (==) = \x y -> isJust (testEquality x y)

instance TestEquality (Expr ids) where
  testEquality (ValueExpr x) (ValueExpr y) = do
    Refl <- testEquality x y
    return Refl
  testEquality (AppExpr x) (AppExpr y) = do
    Refl <- testEquality x y
    return Refl
  testEquality _ _ = Nothing

instance HasRepr (Expr ids) TypeRepr where
  typeRepr (ValueExpr v) = typeRepr v
  typeRepr (AppExpr a) = typeRepr a

asApp :: Expr ids tp -> Maybe (App (Expr ids) tp)
asApp (AppExpr   a) = Just a
asApp (ValueExpr v) = fmapFC ValueExpr <$> valueAsApp v

asArchFn :: Expr ids tp -> Maybe (X86PrimFn (Value X86_64 ids) tp)
asArchFn (ValueExpr (AssignedValue (Assignment _ (EvalArchFn a _)))) = Just a
asArchFn _ = Nothing

app :: App (Expr ids) tp -> Expr ids tp
app = AppExpr

asBoolLit :: Expr ids BoolType -> Maybe Bool
asBoolLit (ValueExpr (BoolValue b)) = Just b
asBoolLit _ = Nothing

-- | If expression is a literal bitvector, then return as an unsigned integer.
asUnsignedBVLit :: Expr ids (BVType w) -> Maybe Integer
asUnsignedBVLit (ValueExpr (BVValue w v)) = Just (toUnsigned w v)
asUnsignedBVLit _ = Nothing

-- | If expression is a literal bitvector, then return as an signed integer.
asSignedBVLit :: Expr ids (BVType w) -> Maybe Integer
asSignedBVLit (ValueExpr (BVValue w v)) = Just (toSigned w v)
asSignedBVLit _ = Nothing

------------------------------------------------------------------------
-- PreBlock

-- | A block that we have not yet finished.
data PreBlock ids = PreBlock { _pBlockStmts :: !(Seq (Stmt X86_64 ids))
                             , _pBlockState :: !(RegState X86Reg (Value X86_64 ids))
                             , _pBlockApps  :: !(MapF (App (Value X86_64 ids)) (Assignment X86_64 ids))
                             , pBlockStart  :: !(ArchSegmentOff X86_64)
                             }

-- | Create a new pre block.
emptyPreBlock :: ArchSegmentOff X86_64
              -> RegState X86Reg (Value X86_64 ids)
              -> PreBlock ids
emptyPreBlock startAddr s  =
  PreBlock { _pBlockStmts = Seq.empty
           , _pBlockApps  = MapF.empty
           , _pBlockState = s
           , pBlockStart  = startAddr
           }

pBlockStmts :: Simple Lens (PreBlock ids) (Seq (Stmt X86_64 ids))
pBlockStmts = lens _pBlockStmts (\s v -> s { _pBlockStmts = v })

pBlockState :: Simple Lens (PreBlock ids) (RegState X86Reg (Value X86_64 ids))
pBlockState = lens _pBlockState (\s v -> s { _pBlockState = v })

pBlockApps  :: Simple Lens (PreBlock ids) (MapF (App (Value X86_64 ids)) (Assignment X86_64 ids))
pBlockApps = lens _pBlockApps (\s v -> s { _pBlockApps = v })

-- | Finishes the current block, if it is started.
finishBlock :: PreBlock ids
             -> (RegState X86Reg (Value X86_64 ids) -> TermStmt X86_64 ids)
             -> Block X86_64 ids
finishBlock preBlock term =
  Block { blockStmts = toList (preBlock^.pBlockStmts)
        , blockTerm  = term (preBlock^.pBlockState)
        }

------------------------------------------------------------------------
-- PartialBlock

-- | This describes a code block that may or may not be terminated by
-- a terminal statement.
data PartialBlock ids
   = UnfinishedPartialBlock !(PreBlock ids)
   | FinishedPartialBlock !(Block X86_64 ids)

-- | Return true if the partial block is not yet terminated and the
-- next PC is the given one.
unfinishedAtAddr :: PartialBlock ids -> MemAddr 64 -> Maybe (PreBlock ids)
unfinishedAtAddr (UnfinishedPartialBlock b) next_ip
  | RelocatableValue _ v <- b^.(pBlockState . curIP)
  , v == next_ip =
      Just b
unfinishedAtAddr _ _ = Nothing

-- | Finishes the current block, if it is started.
finishPartialBlock :: PartialBlock ids
                   -> Block X86_64 ids
finishPartialBlock (UnfinishedPartialBlock pre_b) = finishBlock pre_b FetchAndExecute
finishPartialBlock (FinishedPartialBlock blk) = blk

------------------------------------------------------------------------
-- GenState

-- | A state used for the block generator.
data GenState st_s ids = GenState
       { assignIdGen   :: !(NonceGenerator (ST st_s) ids)
         -- ^ 'NonceGenerator' for generating 'AssignId's
       , _blockState   :: !(PreBlock ids)
         -- ^ Block that we are processing.
       , genInitPCAddr  :: !(MemSegmentOff 64)
         -- ^ This is the address of the instruction we are translating.
       , genInstructionSize :: !Int
         -- ^ Number of bytes of instruction we are translating.
       , _genRegUpdates :: !(MapF.MapF X86Reg (Value X86_64 ids))
         -- ^ The registers updated (along with their new macaw values) during
         -- the evaluation of a single instruction
       , avxMode      :: !Bool
         {- ^ This indicates if we are translating
           an AVX instruction. If so, writing to
           an XMM register also clears that upper
           128-bit of the corresponding YMM register.
           This does not happen, however, if we we
           are working with an SSE instruction. -}
       }

genRegUpdates :: Simple Lens (GenState st_s ids) (MapF.MapF X86Reg (Value X86_64 ids))
genRegUpdates = lens _genRegUpdates (\s v -> s { _genRegUpdates = v })

-- | Blocks that are not in CFG that end with a FetchAndExecute,
-- which we need to analyze to compute new potential branch targets.
blockState :: Lens (GenState st_s ids) (GenState st_s ids) (PreBlock ids) (PreBlock ids)
blockState = lens _blockState (\s v -> s { _blockState = v })

curX86State :: Simple Lens (GenState st_s ids) (RegState X86Reg (Value X86_64 ids))
curX86State = blockState . pBlockState

------------------------------------------------------------------------
-- X86Generator

-- | X86Generator is used to construct basic blocks from a stream of instructions
-- using the semantics.
--
-- It is implemented as a state monad in a continuation passing style so that
-- we can perform symbolic branches.
--
-- This returns either a failure message or the next state.
newtype X86Generator st_s ids a =
  X86G { unX86G ::
           ContT (PartialBlock ids)
                 (ReaderT (GenState st_s ids)
                          (ExceptT Text (ST st_s))) a
       }
  deriving (Applicative, Functor)

-- The main reason for this definition to be given explicitly is so that fail
-- uses throwError instead of the underlying fail in ST
instance Monad (X86Generator st_s ids) where
  return v = seq v $ X86G $ return v
  (X86G m) >>= h = X86G $ m >>= \v -> seq v (unX86G (h v))
  X86G m >> X86G n = X86G $ m >> n
#if __GLASGOW_HASKELL__ < 808
  fail = Control.Monad.Fail.fail
#endif

instance MonadFail (X86Generator st_s ids) where
  fail msg = seq t $ X86G $ ContT $ \_ -> throwError t
    where t = Text.pack msg

-- | The type of an 'X86Generator' continuation
type X86GCont st_s ids a
  =  a
  -> GenState st_s ids
  -> ExceptT Text (ST st_s) (PartialBlock ids)

-- | Run an 'X86Generator' starting from a given state
runX86Generator :: GenState st_s ids
                -> X86Generator st_s ids ()
                -> ExceptT Text (ST st_s) (PartialBlock ids)
runX86Generator st (X86G m) = runReaderT (runContT m (ReaderT . k)) st
  where k () s = pure $! UnfinishedPartialBlock (s^.blockState)

getState :: X86Generator st_s ids (GenState st_s ids)
getState = X86G ask

modGenState :: State (GenState st_s ids) a -> X86Generator st_s ids a
modGenState m = X86G $ ContT $ \c -> ReaderT $ \s ->
  let (a,s') = runState m s
   in runReaderT (c a) s'

-- | Return the value associated with the given register.
getRegValue :: X86Reg tp -> X86Generator st_s ids (Value X86_64 ids tp)
getRegValue r = view (curX86State . boundValue r) <$> getState

-- | Collect state modifications by a single instruction into a single 'ArchState' statement
--
-- See @Data.Macaw.SemMC.Generator.asATomicStateUpdate@, which this is
-- based on and analogous to. The @setRegVal@ mentioned there
-- corresponds to 'setReg' in this module.
asAtomicStateUpdate :: MemAddr 64
                       -- ^ Instruction address
                    -> X86Generator st_s ids a
                       -- ^ An action recording the state transformations of the instruction
                    -> X86Generator st_s ids a
asAtomicStateUpdate insnAddr transformer = do
  modGenState $ genRegUpdates .= MapF.empty
  res <- transformer
  updates <- _genRegUpdates <$> getState
  addStmt (ArchState insnAddr updates)
  return res

-- | Set the value associated with the given register.
setReg :: X86Reg tp -> Value X86_64 ids tp -> X86Generator st_s ids ()
setReg r v = modGenState $ do
  genRegUpdates %= MapF.insert r v
  curX86State . boundValue r .= v

-- | Add a statement to the list of statements.
addStmt :: Stmt X86_64 ids -> X86Generator st_s ids ()
addStmt stmt = seq stmt $
  modGenState $ blockState . pBlockStmts %= (Seq.|> stmt)

addArchStmt :: X86Stmt (Value X86_64 ids) -> X86Generator st_s ids ()
addArchStmt = addStmt . ExecArchStmt

-- | execute a primitive instruction.
addArchTermStmt :: X86TermStmt ids -> X86Generator st ids ()
addArchTermStmt ts = addTermStmt (ArchTermStmt ts)

-- | Terminate the current block immediately
--
-- This can be used to signal an error (e.g., by using the TranslateError terminator)
addTermStmt :: (RegState (ArchReg X86_64) (Value X86_64 ids) -> TermStmt X86_64 ids) -> X86Generator st ids a
addTermStmt ts =
  X86G $ ContT $ \_ -> ReaderT $ \s0 -> do
    let p_b = s0 ^. blockState
    let fin_b = finishBlock p_b ts
    return $! FinishedPartialBlock fin_b

-- | Are we in AVX mode?
isAVX :: X86Generator st ids Bool
isAVX = do gs <- getState
           return $! avxMode gs

-- | Set the AVX mode.
-- See also: 'inAVX'.
setAVX :: Bool -> X86Generator st ids ()
setAVX b = modGenState $ modify $ \g -> g { avxMode = b }

-- | Switch to AVX mode for the duration
-- of the computation, then restore the
-- original mode.
inAVX :: X86Generator st ids a -> X86Generator st ids a
inAVX m =
  do old <- isAVX
     setAVX True
     a <- m
     setAVX old
     return a

-- | Create a new assignment identifier
newAssignID :: X86Generator st_s ids (AssignId ids tp)
newAssignID = do
  gs <- getState
  liftM AssignId $ X86G $ lift $ lift $ lift $ freshNonce $ assignIdGen gs

addAssignment :: AssignRhs X86_64 (Value X86_64 ids) tp
              -> X86Generator st_s ids (Assignment X86_64 ids tp)
addAssignment rhs = do
  l <- newAssignID
  let a = Assignment l rhs
  addStmt $ AssignStmt a
  pure $! a

evalAssignRhs :: AssignRhs X86_64 (Value X86_64 ids) tp
              -> X86Generator st_s ids (Expr ids tp)
evalAssignRhs rhs =
  ValueExpr . AssignedValue <$> addAssignment rhs

-- | Evaluate an architecture-specific function and return the resulting expr.
evalArchFn :: X86PrimFn (Value X86_64 ids) tp
          -> X86Generator st_s ids (Expr ids tp)
evalArchFn f = evalAssignRhs (EvalArchFn f (typeRepr f))


------------------------------------------------------------------------
-- Evaluate expression

-- | This function does a top-level constant propagation/constant reduction.
-- We assume that the leaf nodes have also been propagated (i.e., we only operate
-- at the outermost term)
constPropagate :: forall ids tp. App (Value X86_64 ids) tp -> Maybe (Value X86_64 ids tp)
constPropagate v =
  case v of
   BVAnd _ l r
     | Just _ <- testEquality l r -> Just l
   BVAnd sz l r                   -> binop (.&.) sz l r
   -- Units
   BVAdd _  l (BVValue _ 0)       -> Just l
   BVAdd _  (BVValue _ 0) r       -> Just r
   BVAdd sz l r                   -> binop (+) sz l r
   BVMul _  l (BVValue _ 1)       -> Just l
   BVMul _  (BVValue _ 1) r       -> Just r

   UExt  (BVValue _ n) sz         -> Just $ mkLit sz n

   -- Word operations
   Trunc (BVValue _ x) sz         -> Just $ mkLit sz x

   -- Boolean operations
   BVUnsignedLt l r               -> boolop (<) l r
   Eq l r                         -> boolop (==) l r
   BVComplement sz x              -> unop complement sz x
   _                              -> Nothing
  where
    boolop :: (Integer -> Integer -> Bool)
           -> Value X86_64 ids utp
           -> Value X86_64 ids utp
           -> Maybe (Value X86_64 ids BoolType)
    boolop f (BVValue _ l) (BVValue _ r) = Just $ BoolValue (f l r)
    boolop _ _ _ = Nothing

    unop :: (tp ~ BVType n)
         => (Integer -> Integer)
         -> NatRepr n -> Value X86_64 ids tp -> Maybe (Value X86_64 ids tp)
    unop f sz (BVValue _ l)  = Just $ mkLit sz (f l)
    unop _ _ _               = Nothing

    binop :: (tp ~ BVType n) => (Integer -> Integer -> Integer)
          -> NatRepr n
          -> Value X86_64 ids tp
          -> Value X86_64 ids tp
          -> Maybe (Value X86_64 ids tp)
    binop f sz (BVValue _ l) (BVValue _ r) = Just $ mkLit sz (f l r)
    binop _ _ _ _                          = Nothing

evalApp :: App (Value X86_64 ids) tp -> X86Generator st_s ids (Value X86_64 ids tp)
evalApp a = do
  case constPropagate a of
    Nothing -> do
      s <- getState
      case MapF.lookup a (s^.blockState^.pBlockApps) of
        Nothing -> do
          r <- addAssignment (EvalApp a)
          modGenState $ blockState . pBlockApps %= MapF.insert a r
          return (AssignedValue r)
        Just r -> return (AssignedValue r)
    Just v  -> return v


eval :: Expr ids tp -> X86Generator st_s ids (Value X86_64 ids tp)
eval (ValueExpr v) = return v
eval (AppExpr a) = evalApp =<< traverseFC eval a
