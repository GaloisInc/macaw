{-
This code associates upper bounds with parts of registers and
addresses in the stack.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.AbsDomain.JumpBounds
  ( -- * Initial jump bounds
    InitJumpBounds
  , functionStartBounds
  , joinInitialBounds
  , ppInitJumpBounds
    -- * IntraJumpbounds
  , IntraJumpBounds
  , mkIntraJumpBounds
  , execStatement
  , postCallBounds
  , nextBlockBounds
  , assertPred
  , unsignedUpperBound
  , stackOffset
  , UpperBound(..)
    -- * Low-level details
  , locRep
  , BoundLoc(..)
  , ClassPred(..)
  ) where

import           Control.Monad.Reader
import           Control.Monad.ST
import           Control.Monad.State
import           Data.Functor
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce
import           Data.Parameterized.TraversableFC
import           Data.STRef
import           Data.Word
import           GHC.Stack
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.AbsDomain.CallParams
import           Data.Macaw.CFG.App
import           Data.Macaw.CFG.Core
import           Data.Macaw.Memory
import           Data.Macaw.Types hiding (Type)
import qualified Data.Macaw.Types as M


addrTypeRepr :: MemWidth w => TypeRepr (BVType w)
addrTypeRepr = BVTypeRepr memWidthNatRepr

------------------------------------------------------------------------
-- Utilities

mapTraverseWithKey_ :: Applicative m => (k -> a -> m ()) -> Map k a -> m ()
mapTraverseWithKey_ f = Map.foldrWithKey (\k v r -> f k v *> r) (pure ())

------------------------------------------------------------------------
-- Changed

-- | A monad that can be used to record when a value is changed.
type Changed s = ReaderT (STRef s Bool) (ST s)

-- | Record the value has changed if the Boolean is true.
markChanged :: Bool -> Changed s ()
markChanged False = pure ()
markChanged True = do
  r <- ask
  lift $ writeSTRef r True

runChanged :: forall a . (forall s . Changed s a) -> Maybe a
runChanged action = runST $ do
  r <-  newSTRef False
  a <- runReaderT action r
  b <- readSTRef r
  pure $! if b then Just a else Nothing

------------------------------------------------------------------------
-- KeyPair

data KeyPair (key :: k -> Type)  (tp :: k) = KeyPair !(key tp) !(key tp)

instance TestEquality k => TestEquality (KeyPair k) where
  testEquality (KeyPair x1 x2) (KeyPair y1 y2) = do
    Refl <- testEquality x1 y1
    testEquality x2 y2

instance OrdF k => OrdF (KeyPair k) where
  compareF (KeyPair x1 x2) (KeyPair y1 y2) =
    joinOrderingF (compareF x1 y1) (compareF x2 y2)

------------------------------------------------------------------------
-- UpperBound

-- | An upper bound on a value.
data UpperBound tp where
  -- | @IntegerUpperBound b v@ indicates the low @b@ bits of the value
  -- are at most @v@ when the bitvector is treated as an unsigned
  -- integer.
  UBVUpperBound :: (u <= w) => !(NatRepr u) -> !Natural -> UpperBound (BVType w)

------------------------------------------------------------------------
-- ClassPred

-- | This describes a constraint associated with an equivalence class
-- of registers in @InitJumpBounds@.
data ClassPred (w :: Nat) tp where
  -- | Value is a bitvector with the given upper bound.  The argument
  -- is the upper bound of the bitvector when interpreted as a
  -- unsigned number.
  BoundedBV :: !(UpperBound tp)
            -> ClassPred w tp
  -- | Value is a offset of the stack pointer at the given offset argument.
  IsStackOffset :: {-# UNPACK #-} !(MemInt w)
              -> ClassPred w (BVType w)
  -- | No constraints on value.
  TopPred :: ClassPred w tp


ppAddend :: MemInt w -> Doc
ppAddend o | memIntValue o < 0 = text "-" <+> pretty (negate (toInteger (memIntValue o)))
           | otherwise = text "+" <+> pretty o

-- | Pretty print the class predicate
ppClassPred :: Doc -> ClassPred w tp -> Doc
ppClassPred d (BoundedBV (UBVUpperBound w b)) =
  d <> text ":[" <> text (show w) <> text "] <= " <> text (show b)
ppClassPred d (IsStackOffset i) =
  d <+> text "= stack_frame" <+> ppAddend i
ppClassPred _d TopPred =
  text ""

-- | Take the union of the old and new constraint, and record if the
-- old constraint was weakened by the new constraint.
joinClassPred :: ClassPred w tp
              -> ClassPred w tp
              -> Changed s (ClassPred w tp)
joinClassPred old new =
  case (old,new) of
    (BoundedBV (UBVUpperBound u x), BoundedBV (UBVUpperBound v y))
      | Just Refl <- testEquality u v ->
        markChanged (x < y) $> BoundedBV (UBVUpperBound u (max x y))
    (IsStackOffset i, IsStackOffset j)
      | i == j -> pure $! old
    (TopPred,_) -> pure TopPred
    (_,_) -> markChanged True $> TopPred

------------------------------------------------------------------------
-- BoundLoc

-- | Either a register or stack offset.
--
-- These locations are tracked by our bounds analysis algorithm.
data BoundLoc r tp where
  RegLoc :: !(r tp) -> BoundLoc r tp
  StackOffLoc :: !(MemInt (RegAddrWidth r))
              -> !(MemRepr tp)
              -> BoundLoc r tp

instance TestEquality r => TestEquality (BoundLoc r) where
  testEquality (RegLoc x) (RegLoc y) = testEquality x y
  testEquality (StackOffLoc xi xr) (StackOffLoc yi yr) | xi == yi =
    testEquality xr yr
  testEquality _ _ = Nothing

instance HasRepr r TypeRepr => HasRepr (BoundLoc r) TypeRepr where
  typeRepr (RegLoc r) = typeRepr r
  typeRepr (StackOffLoc _ r) = typeRepr r

instance OrdF r => OrdF (BoundLoc r) where
  compareF (RegLoc x) (RegLoc y) = compareF x y
  compareF (RegLoc _) _ = LTF
  compareF _ (RegLoc _) = GTF

  compareF (StackOffLoc xi xr) (StackOffLoc yi yr) =
    case compare xi yi of
      LT -> LTF
      GT -> GTF
      EQ -> compareF xr yr

instance ShowF r => Pretty (BoundLoc r tp) where
  pretty (RegLoc r) = text (showF r)
  pretty (StackOffLoc i tp) = text "*(stack_frame " <+> ppAddend i <> text ") :" <> pretty tp

------------------------------------------------------------------------
-- LocConstraint

-- | A constraint on a @BoundLoc
data LocConstraint r tp where
  ValueRep :: !(ClassPred (RegAddrWidth r) tp)
           -> !Word64
           -> LocConstraint r tp -- ^ An equivalence class
                                   -- representative with the given
                                   -- number of elements.
                                   --
                                   -- In our map the number of
                                   -- equivalence class members should always be positive.
  EqualValue :: !(BoundLoc r tp)
             -> LocConstraint r tp

unconstrained :: LocConstraint r tp
unconstrained = ValueRep TopPred 1

ppLocConstraint :: ShowF r => Doc -> LocConstraint r tp -> Doc
ppLocConstraint d (ValueRep p _cnt) = ppClassPred d p
ppLocConstraint d (EqualValue v) = d <+> text "=" <+> pretty v

------------------------------------------------------------------------
-- MemAnn

-- | A value with a particular type along with a MemRepr indicating
-- how the type is encoded in memory.
data MemAnn (p :: M.Type -> Type) =
  forall (tp :: M.Type) . MemAnn !(MemRepr tp) !(p tp)

ppMemConstraint :: ShowF r => MemInt (RegAddrWidth r) -> MemAnn (LocConstraint r) -> Doc
ppMemConstraint i (MemAnn repr cns) =
  let nm = text "*(stack_frame" <+> ppAddend i <> text "," <+> pretty repr <> text "):"
   in ppLocConstraint nm cns

------------------------------------------------------------------------
-- StackMap

type StackMap w p = Map (MemInt w) (MemAnn p)

stackMapLookup :: MemInt w -> MemRepr tp -> StackMap w p -> Maybe (p tp)
stackMapLookup i repr m =
  case Map.lookup i m of
    Just (MemAnn defRepr p) ->
      case testEquality repr defRepr of
        Just Refl -> Just p
        Nothing -> Nothing
    Nothing -> Nothing

clearPreWrites :: Ord i => i -> i -> Map i v -> Map i v
clearPreWrites l h m =
  case Map.lookupLT h m of
    Just (o,_v) | o >= l -> clearPreWrites l h (Map.delete o m)
    _ -> m

clearPostWrites :: Ord i => i -> i -> Map i v -> Map i v
clearPostWrites l h m =
  case Map.lookupGE l m of
    Just (o,_v) | o < h -> clearPostWrites l h (Map.delete o m)
    _ -> m

-- | Update the stack to point to the given expression.
stackMapInsert :: forall w p tp
               .  MemWidth w
               => MemInt w
               -> MemRepr tp
               -> p tp
               -> StackMap w p
               -> StackMap w p
stackMapInsert off repr v m =
  let e = off + fromIntegral (memReprBytes repr)
   in Map.insert off (MemAnn repr v) $
      clearPreWrites off e $
      clearPostWrites off e m

------------------------------------------------------------------------
-- InitialIndexBiunds

-- | Bounds for a function as the start of a block.
data InitJumpBounds arch
   = InitJumpBounds { initialRegBoundMap :: !(MapF (ArchReg arch) (LocConstraint (ArchReg arch)))
                      -- ^ Maps each register to the bounds on it.
                    , initialStackMap :: !(StackMap (ArchAddrWidth arch) (LocConstraint (ArchReg arch)))
                      -- ^ Maps stack offsets to the memory constraint.
                    }

ppInitJumpBounds :: forall arch . ShowF (ArchReg arch) => InitJumpBounds arch -> [Doc]
ppInitJumpBounds bnds
  = flip (MapF.foldrWithKey (\k v -> (ppLocConstraint (text (showF k)) v:)))
         (initialRegBoundMap bnds) $
    Map.foldrWithKey (\i v -> (ppMemConstraint i v:)) [] (initialStackMap bnds)

instance ShowF (ArchReg arch) => Pretty (InitJumpBounds arch) where
  pretty = vcat . ppInitJumpBounds

instance ShowF (ArchReg arch) => Show (InitJumpBounds arch) where
  show = show . pretty

-- | Bounds at start of function.
functionStartBounds :: RegisterInfo (ArchReg arch) => InitJumpBounds arch
functionStartBounds = InitJumpBounds { initialRegBoundMap =
                                             MapF.singleton sp_reg (ValueRep (IsStackOffset 0) 1)
                                     , initialStackMap = Map.empty
                                     }

emptyInitialBounds :: InitJumpBounds arch
emptyInitialBounds =
  InitJumpBounds { initialRegBoundMap = MapF.empty
                     , initialStackMap = Map.empty
                     }

-- | Return the representative and  predicate associated with the location in the map.
locConstraint :: OrdF (ArchReg arch)
              => InitJumpBounds arch
              -> BoundLoc (ArchReg arch) tp
              -> LocConstraint (ArchReg arch) tp
locConstraint bnds (RegLoc r) =
  MapF.findWithDefault unconstrained r (initialRegBoundMap bnds)
locConstraint bnds (StackOffLoc i repr) =
  case stackMapLookup i repr (initialStackMap bnds) of
    Just cns -> cns
    Nothing -> unconstrained

-- | Return the representative and predicate associated with the
-- location in the map along with the class size.
locRep :: OrdF (ArchReg arch)
       => InitJumpBounds arch
       -> BoundLoc (ArchReg arch) tp
       -> (BoundLoc (ArchReg arch) tp, ClassPred (ArchAddrWidth arch) tp, Word64)
locRep bnds l =
  case locConstraint bnds l of
    EqualValue loc -> locRep bnds loc
    ValueRep p c -> (l, p, c)

-- | Increment the reference count for a class representative.
incLocCount :: OrdF (ArchReg arch)
            => BoundLoc (ArchReg arch) tp
            -> InitJumpBounds arch
            -> InitJumpBounds arch
incLocCount (RegLoc r) bnds =
    bnds { initialRegBoundMap =
             MapF.insertWith upd r (ValueRep TopPred 2) (initialRegBoundMap bnds)
         }
  where upd _new (ValueRep p cnt) = ValueRep p (cnt+1)
        upd _new (EqualValue _) = error $ "insLocCount given non-class representative."
incLocCount (StackOffLoc off repr) bnds =
    bnds { initialStackMap = Map.insertWith upd off def (initialStackMap bnds) }
  where def = MemAnn repr (ValueRep TopPred 2)
        upd _new (MemAnn oldRepr valCns) =
          case testEquality repr oldRepr of
            Just Refl ->
              case valCns of
                ValueRep p cnt -> MemAnn repr (ValueRep p (cnt+1))
                EqualValue _ -> error $ "insLocCount given non-class representative."
            Nothing ->
              error $ "insLocCount given overlapping memory offsets."

setLocConstraint :: OrdF (ArchReg arch)
                   => BoundLoc (ArchReg arch) tp
                   -> LocConstraint (ArchReg arch) tp
                   -> InitJumpBounds arch
                   -> InitJumpBounds arch
setLocConstraint (RegLoc r) c bnds =
  bnds { initialRegBoundMap = MapF.insert r c (initialRegBoundMap bnds) }
setLocConstraint (StackOffLoc i repr) c bnds =
  bnds { initialStackMap = Map.insert i (MemAnn repr c) (initialStackMap bnds) }

assertNewLocEqual :: OrdF (ArchReg arch)
                  => BoundLoc (ArchReg arch) tp
                     -- ^ New location that should be unbound in this
                     -- result.
                  -> BoundLoc (ArchReg arch) tp
                     -- ^ Existing class representative
                  -> InitJumpBounds arch
                  -> InitJumpBounds arch
assertNewLocEqual newLoc loc =
  incLocCount loc . setLocConstraint newLoc (EqualValue loc)

addNewClassRep :: OrdF (ArchReg arch)
               => BoundLoc (ArchReg arch) tp
               -> ClassPred (ArchAddrWidth arch) tp
               -> InitJumpBounds arch
               -> InitJumpBounds arch
addNewClassRep _r TopPred bnds = bnds
addNewClassRep loc p bnds = setLocConstraint loc (ValueRep p 1) bnds

-- | Join locations
joinNewLoc :: forall s arch tp
           .  OrdF (ArchReg arch)
           => InitJumpBounds arch
           -> InitJumpBounds arch
           -> STRef s (InitJumpBounds arch)
           -- ^ The current index bounds.
           -> STRef s (MapF (KeyPair (BoundLoc (ArchReg arch))) (BoundLoc (ArchReg arch)))
           -- ^ The map from (oldClassRep, newClassRep) pairs to the
           -- result class rep.
           -> STRef s Int
           -- ^ Stores the number of equivalence classes we have seen in
           -- in the old class
           -- Used so determining if any classes are changed.
           -> BoundLoc (ArchReg arch) tp
              -- ^ Location in join that we have not yet visited.
           -> LocConstraint (ArchReg arch) tp
              -- ^ Constraint on location in original list.
           -> Changed s ()
joinNewLoc old new bndsRef procRef cntr thisLoc oldCns = do
  (oldRep, oldPred, _oldCnt) <- lift $
    case oldCns of
      ValueRep p c -> do
        -- Increment number of equivalence classes when we see an old
        -- representative.
        modifySTRef' cntr (+1)
        -- Return this loc
        pure (thisLoc, p, c)
      EqualValue  oldLoc ->
        pure (locRep old oldLoc)
  let (newRep, newPred, _newCnt) = locRep new thisLoc
  m <- lift $ readSTRef procRef
  -- See if we have already added a representative for this class.
  let pair = KeyPair oldRep newRep
  case MapF.lookup pair m of
    Nothing -> do
      p <- joinClassPred oldPred newPred
      lift $ do
        writeSTRef procRef $! MapF.insert pair thisLoc m
        modifySTRef' bndsRef $ addNewClassRep thisLoc p
    Just resRep ->
      -- Assert r is equal to resRep
      lift $ modifySTRef' bndsRef $ assertNewLocEqual thisLoc resRep

-- | Return a jump bounds that implies both input bounds, or `Nothing`
-- if every fact inx the old bounds is implied by the new bounds.
joinInitialBounds :: forall arch
                  .  MapF.OrdF (ArchReg arch)
                  => InitJumpBounds arch
                  -> InitJumpBounds arch
                  -> Maybe (InitJumpBounds arch)
joinInitialBounds old new = runChanged $ do
  -- Reference to new bounds.
  bndsRef <- lift $ newSTRef emptyInitialBounds
  -- This maps pairs containing the class representative in the old
  -- and new maps to the associated class representative in the
  -- combined bounds.
  procRef <- lift $ newSTRef MapF.empty
  cntr    <- lift $ newSTRef 0
  --
  MapF.traverseWithKey_
    (\r -> joinNewLoc old new bndsRef procRef cntr (RegLoc r))
    (initialRegBoundMap old)
  mapTraverseWithKey_
    (\i (MemAnn r c) -> joinNewLoc old new bndsRef procRef cntr (StackOffLoc i r) c)
    (initialStackMap old)

  -- Check number of equivalence classes in result and original
  -- The count should not have decreased, but may increase if two elements
  -- are no longer equal, and we need to check this.
  origClassCount <- lift $ readSTRef cntr
  resultClassCount <- lift $ MapF.size <$> readSTRef procRef
  unless (origClassCount <= resultClassCount) $ do
    error "Original class count should be bound by resultClassCount"
  -- Record changed if any classes are different.
  markChanged (origClassCount < resultClassCount)

  lift $ readSTRef bndsRef

combineUpperBound :: UpperBound (BVType w) -> ClassPred a (BVType w) -> ClassPred a (BVType w)
combineUpperBound ubnd oldp  =
  case oldp of
    TopPred -> BoundedBV ubnd      -- Prefer newbound.
    BoundedBV _ -> BoundedBV ubnd  -- Prefer newbound
    IsStackOffset _ -> oldp -- Prefer stackoffset

-- | Add a upper bound to a class representative
addClassRepBound :: ( HasCallStack
                    , OrdF (ArchReg arch)
                    , MemWidth (ArchAddrWidth arch)
                    )
                 => BoundLoc (ArchReg arch) (BVType w)
                 -- ^ The location to update.
                 --
                 -- This should be a class representative in the initial state.
                 -- bounds.
                 -> UpperBound (BVType w)
                 -> InitJumpBounds arch
                 -> InitJumpBounds arch
addClassRepBound (RegLoc r) ubnd bnds =
  let p0 = ValueRep (BoundedBV ubnd) 1
      upd (EqualValue _) = error "addClassBounds expected class rep"
      upd (ValueRep oldp cnt) = ValueRep (combineUpperBound ubnd oldp) cnt
   in bnds { initialRegBoundMap = MapF.insertWith (\_ -> upd) r p0 (initialRegBoundMap bnds) }
addClassRepBound (StackOffLoc i repr) ubnd bnds =
  let r = case stackMapLookup i repr (initialStackMap bnds) of
            Nothing -> ValueRep (BoundedBV ubnd) 1
            Just (EqualValue _) -> error "addClassBounds expected class rep"
            Just (ValueRep oldp cnt) -> ValueRep (combineUpperBound ubnd oldp) cnt
   in bnds { initialStackMap = stackMapInsert i repr r (initialStackMap bnds) }

------------------------------------------------------------------------
-- BoundExpr

-- | This is an expression that represents the value of stack
-- locations and assignments during steping through the block.
--
-- The main diference between this and
-- the `Value` type, index expressions do not depend on values read
-- and written to memory during execution of the block, and are purely
-- functions of the input
--
-- This is different from `ClassPred` in that @ClassPred@ is a property
-- assigned to equivalence classes
data BoundExpr arch ids s tp where
  -- | This refers to the contents of the location at the start
  -- of block execution.
  --
  -- The location should be a class representative in the initial bounds.
  ClassRepExpr :: !(BoundLoc (ArchReg arch) tp) -> BoundExpr arch ids s tp
  -- | An assignment that is not interpreted, and just treated as a constant.
  AssignExpr :: !(AssignId ids tp)
             -> !(TypeRepr tp)
             -> BoundExpr arch ids s tp
  -- | Denotes the value of the stack pointer at function start plus some constant.
  StackOffsetExpr :: !(MemInt (ArchAddrWidth arch))
                  -> BoundExpr arch ids s (BVType (ArchAddrWidth arch))
  -- | Denotes a constant
  CExpr :: !(CValue arch tp) -> BoundExpr arch ids s tp
  -- | This is a pure function applied to other index expressions that
  -- does not seem to be a stack offset or assignment.
  AppExpr :: !(Nonce s tp)
          -> !(App (BoundExpr arch ids s) tp)
          -> BoundExpr arch ids s tp

instance TestEquality (ArchReg arch) => TestEquality (BoundExpr arch ids s) where
  testEquality (ClassRepExpr x) (ClassRepExpr y) =
    testEquality x y
  testEquality (AssignExpr x _) (AssignExpr y _) =
    testEquality x y
  testEquality (StackOffsetExpr x) (StackOffsetExpr y) =
    if x == y then
      Just Refl
     else
      Nothing
  testEquality (CExpr x) (CExpr y) =
    testEquality x y
  testEquality (AppExpr xn _xa) (AppExpr yn _ya) =
    testEquality xn yn
  testEquality _ _ = Nothing

instance OrdF (ArchReg arch) => OrdF (BoundExpr arch ids s) where
  compareF (ClassRepExpr x) (ClassRepExpr y) = compareF x y
  compareF ClassRepExpr{} _ = LTF
  compareF _ ClassRepExpr{} = GTF

  compareF (AssignExpr x _) (AssignExpr y _) = compareF x y
  compareF AssignExpr{} _ = LTF
  compareF _ AssignExpr{} = GTF


  compareF (StackOffsetExpr x) (StackOffsetExpr y) = fromOrdering (compare x y)
  compareF StackOffsetExpr{} _ = LTF
  compareF _ StackOffsetExpr{} = GTF

  compareF (CExpr x) (CExpr y) = compareF x y
  compareF CExpr{} _ = LTF
  compareF _ CExpr{} = GTF

  compareF (AppExpr xn _xa) (AppExpr yn _ya) = compareF xn yn

instance ( HasRepr (ArchReg arch) TypeRepr
         , MemWidth (ArchAddrWidth arch)
         ) => HasRepr (BoundExpr arch ids s) TypeRepr where
  typeRepr e =
    case e of
      ClassRepExpr x    -> typeRepr x
      AssignExpr _ tp   -> tp
      StackOffsetExpr _ -> addrTypeRepr
      CExpr x           -> typeRepr x
      AppExpr _ a       -> typeRepr a

-- | Return an expression equivalent to the location in the bounds.
--
-- This attempts to normalize the expression to get a representative.
locExpr :: OrdF (ArchReg arch)
        => InitJumpBounds arch
        -> BoundLoc (ArchReg arch) tp
        -> BoundExpr arch ids s tp
locExpr bnds loc =
  case locRep bnds loc of
    (_, IsStackOffset i, _) -> StackOffsetExpr i
    (rep, BoundedBV _, _) -> ClassRepExpr rep
    (rep, TopPred, _) -> ClassRepExpr rep

------------------------------------------------------------------------
-- IntraJumpBounds

-- | Information about bounds for a particular value within a block.
data IntraJumpBounds arch ids s
   = IntraJumpBounds { initBounds :: !(InitJumpBounds arch)
                       -- ^ Initial bounds at execution start.
                     , stackExprMap :: !(StackMap (ArchAddrWidth arch) (BoundExpr arch ids s))
                        -- ^ Maps stack offsets to the expression associated with them.
                     , assignExprMap :: !(MapF (AssignId ids) (BoundExpr arch ids s))
                       -- ^ Maps processed assignments to index expressions.
                     , assignBoundMap :: !(MapF (AssignId ids) UpperBound)
                       -- ^ Maps assignments to any asserted upper bound infor,ation.
                     , appBoundMap :: !(MapF (Nonce s) UpperBound)
                       -- ^ Maps app expression nonce to the upper bound.
                     , memoTable :: !(MapF (App (BoundExpr arch ids s)) (BoundExpr arch ids s))
                       -- ^ Table for ensuring each bound expression
                       -- has a single representative.
                     }

-- | Create index bounds from initial index bounds.
mkIntraJumpBounds :: forall arch ids s
                  .  OrdF (ArchReg arch)
                  => InitJumpBounds arch
                  -> IntraJumpBounds arch ids s
mkIntraJumpBounds initBnds = do
  let -- Map stack offset and memory annotation pair to the
      -- representative in the initial bounds.
      stackExpr :: MemInt (ArchAddrWidth arch)
                -> MemAnn (LocConstraint (ArchReg arch))
                -> MemAnn (BoundExpr arch ids s)
      stackExpr i (MemAnn tp _) = MemAnn tp (locExpr initBnds (StackOffLoc i tp))
   in IntraJumpBounds { initBounds     = initBnds
                      , stackExprMap   = Map.mapWithKey stackExpr (initialStackMap initBnds)
                      , assignExprMap  = MapF.empty
                      , assignBoundMap = MapF.empty
                      , appBoundMap    = MapF.empty
                      , memoTable      = MapF.empty
                      }

-- | Return the value of the index expression given the bounds.
valueExpr :: forall arch ids s tp
          .  OrdF (ArchReg arch)
          => IntraJumpBounds arch ids s
          -> Value arch ids tp
          -> BoundExpr arch ids s tp
valueExpr bnds val =
  case val of
    CValue c -> CExpr c
    AssignedValue (Assignment aid _) ->
      case MapF.lookup aid (assignExprMap bnds) of
        Just e -> e
        Nothing -> error $ "valueExpr internal: Expected value to be assigned."
    Initial r -> locExpr (initBounds bnds) (RegLoc r)

-- | Return stack offset if value is a stack offset.
stackOffset :: OrdF (ArchReg arch)
            => IntraJumpBounds arch ids s
            -> Value arch ids (BVType (ArchAddrWidth arch))
            -> Maybe (MemInt (ArchAddrWidth arch))
stackOffset bnds val =
  case valueExpr bnds val of
    StackOffsetExpr i -> Just i
    _ -> Nothing

bindAssignment :: IntraJumpBounds arch ids s
              -> AssignId ids tp
              -> BoundExpr arch ids s tp
              -> IntraJumpBounds arch ids s
bindAssignment bnds aid expr =
  bnds { assignExprMap = MapF.insert aid expr (assignExprMap bnds) }

-- | Update the stack to point to the given expression.
writeStackOff :: forall arch ids s tp
              .  MemWidth (ArchAddrWidth arch)
              => IntraJumpBounds arch ids s
              -> MemInt (ArchAddrWidth arch)
              -> MemRepr tp
              -> BoundExpr arch ids s tp
              -> IntraJumpBounds arch ids s
writeStackOff bnds off repr v =
  bnds { stackExprMap = stackMapInsert off repr v (stackExprMap bnds) }

-- | Return an index expression associated with the @AssignRhs@.
rhsExpr :: forall arch ids s tp
        .  ( MemWidth (ArchAddrWidth arch)
           , OrdF (ArchReg arch)
           )
        => NonceGenerator (ST s) s
        -> IntraJumpBounds arch ids s
        -> AssignId ids tp
        -> AssignRhs arch (Value arch ids) tp
        -> ST s (BoundExpr arch ids s tp)
rhsExpr gen bnds aid arhs =
  case arhs of
    EvalApp app -> do
      let stackFn v = toInteger <$> stackOffset bnds v
      case appAsStackOffset stackFn app of
        Just (StackOffsetView o) -> do
          pure $ StackOffsetExpr $ fromInteger o
        _ -> do
          let a = fmapFC (valueExpr bnds) app
          case MapF.lookup a (memoTable bnds) of
            Just r -> do
              pure r
            Nothing -> do
              (`AppExpr` a) <$> freshNonce gen
    ReadMem addr repr
      | Just o <- stackOffset bnds addr
      , Just e <- stackMapLookup o repr (stackExprMap bnds) -> do
          pure e
    _ -> do
      pure $! AssignExpr aid (typeRepr arhs)

-- | Given a statement this modifies the bounds based on the statement.
execStatement :: ( MemWidth (ArchAddrWidth arch)
                 , OrdF (ArchReg arch)
                 )
              => NonceGenerator (ST s) s
              -> IntraJumpBounds arch ids s
              -> Stmt arch ids
              -> ST s (IntraJumpBounds arch ids s)
execStatement gen bnds stmt =
  case stmt of
    AssignStmt (Assignment aid arhs) -> do
      let bnds' = case arhs of
                    EvalArchFn{} -> bnds { stackExprMap = Map.empty }
                    _ -> bnds
      bindAssignment bnds' aid <$> rhsExpr gen bnds' aid arhs
    WriteMem addr repr val ->
      case stackOffset bnds addr of
        Just addrOff ->
          pure $! writeStackOff bnds addrOff repr (valueExpr  bnds val)
        -- If we write to something other than stack, then clear all stack references.
        Nothing ->
          pure $! bnds { stackExprMap = Map.empty }
    CondWriteMem{} -> pure $! bnds { stackExprMap = Map.empty }
    InstructionStart{} -> pure $! bnds
    Comment{} -> pure $! bnds
    ExecArchStmt{} -> pure $! bnds { stackExprMap = Map.empty }
    ArchState{} -> pure $! bnds

instance ShowF (ArchReg arch) => Pretty (IntraJumpBounds arch ids s) where
  pretty bnds = pretty (initBounds bnds)

------------------------------------------------------------------------
-- Operations

cvaluePred :: CValue arch tp -> ClassPred (ArchAddrWidth arch) tp
cvaluePred v =
  case v of
    BoolCValue _ -> TopPred
    BVCValue w i -> BoundedBV (UBVUpperBound w (fromInteger i))
    RelocatableCValue{} -> TopPred
    SymbolCValue{} -> TopPred


exprPred :: ( MemWidth (ArchAddrWidth arch)
            , HasRepr (ArchReg arch) TypeRepr
            , OrdF (ArchReg arch)
            )
         => IntraJumpBounds arch ids s
         -> BoundExpr arch ids s tp
         -> ClassPred (ArchAddrWidth arch) tp
exprPred bnds v =
  case v of
    ClassRepExpr loc ->
      case locRep (initBounds bnds) loc of
        (_,p,_) -> p
    AssignExpr n _ -> do
      case MapF.lookup n (assignBoundMap bnds) of
        Just b  -> BoundedBV b
        Nothing -> TopPred
    StackOffsetExpr x -> IsStackOffset x
    CExpr c -> cvaluePred c
    AppExpr n _app
      | Just b <- MapF.lookup n (appBoundMap bnds) ->
          BoundedBV b
    AppExpr _n app ->
      case app of
        BVAnd _ x y ->
          case (exprPred bnds x,  exprPred bnds y) of
            (BoundedBV (UBVUpperBound xw xb), BoundedBV (UBVUpperBound yw yb))
              | Just Refl <- testEquality xw yw ->
                  BoundedBV (UBVUpperBound xw (min xb yb))
            (TopPred, yb) -> yb
            (xb, _)       -> xb
        SExt x w ->
          case exprPred bnds x of
            BoundedBV (UBVUpperBound u b) ->
              case testLeq u w of
                Just LeqProof -> BoundedBV (UBVUpperBound u b)
                Nothing -> error "unsignedUpperBound given bad width"
            _ -> TopPred
        UExt x w ->
          case exprPred bnds x of
            BoundedBV (UBVUpperBound u r) ->
              -- If bound is full width, then we can keep it, otherwise we only have subset.
              case testEquality u (typeWidth x) of
                Just Refl -> BoundedBV (UBVUpperBound w r)
                Nothing ->
                  case testLeq u w of
                    Just LeqProof -> BoundedBV (UBVUpperBound u r)
                    Nothing -> error "unsignedUpperBound given bad width"
            _ -> TopPred
        Trunc x w ->
          case exprPred bnds x of
            BoundedBV (UBVUpperBound u xr) -> BoundedBV $
              case testLeq u w of
                Just LeqProof -> do
                  UBVUpperBound u xr
                Nothing -> do
                  UBVUpperBound w (min xr (fromInteger (maxUnsigned w)))
            _ -> TopPred
        _ -> TopPred

-- | This attempts to resolve the predicate associated with a value.
valuePred :: ( MapF.OrdF (ArchReg arch)
             , MapF.ShowF (ArchReg arch)
             , RegisterInfo (ArchReg arch)
             )
          => IntraJumpBounds arch ids s
          -> Value arch ids tp
          -> ClassPred (ArchAddrWidth arch) tp
valuePred bnds v =
  case v of
    CValue cv -> cvaluePred cv
    AssignedValue a ->
      case MapF.lookup (assignId a) (assignExprMap bnds) of
        Just valExpr -> exprPred bnds valExpr
        Nothing -> TopPred
    Initial r ->
      case locRep (initBounds bnds) (RegLoc r) of
        (_,p,_) -> p

-- | Lookup an upper bound or return analysis for why it is not defined.
unsignedUpperBound :: ( MapF.OrdF (ArchReg arch)
                      , MapF.ShowF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                   => IntraJumpBounds arch ids s
                   -> Value arch ids tp
                   -> Either String (UpperBound tp)
unsignedUpperBound bnds v =
  case valuePred bnds v of
    BoundedBV b -> Right b
    _ -> Left $ "Value has no upper bound."

-- | Add a inclusive upper bound to a value.
--
-- Our operation allows one to set the upper bounds on the low order
-- of an integer.  This is represented by the extra argument `NatRepr
-- u`.
--
-- This either returns the refined bounds, or `Left msg` where `msg`
-- is an explanation of what inconsistency was detected.  The upper
-- bounds must be non-negative.
addUpperBound :: ( MapF.OrdF (ArchReg arch)
                 , HasRepr (ArchReg arch) TypeRepr
                 , u <= w
                 , MemWidth (ArchAddrWidth arch)
                 )
               => BoundExpr arch ids s (BVType w)
                 -- ^ Value we are adding upper bound for.
               -> NatRepr u
                  -- ^ Restrict upper bound to only `u` bits.
               -> Natural
               -- ^ Upper bound as an unsigned number
               -> IntraJumpBounds arch ids s
                 -- ^ Current bounds.
               -> Either String (IntraJumpBounds arch ids s)
addUpperBound v _u bnd bnds
    -- Do nothing if upper bounds equals or exceeds maximum unsigned
    -- value.
  | bnd >= fromInteger (maxUnsigned (typeWidth v)) = Right bnds
addUpperBound v u bnd bnds =
  case v of
    ClassRepExpr loc ->
      pure $ bnds { initBounds = addClassRepBound loc (UBVUpperBound u bnd) (initBounds bnds) }
    AssignExpr aid _ -> do
      pure $ bnds { assignBoundMap = MapF.insert aid (UBVUpperBound u bnd) (assignBoundMap bnds) }
    StackOffsetExpr _i ->
      Right bnds
    CExpr cv ->
      case cv of
        BVCValue _ c | c <= toInteger bnd -> Right bnds
                     | otherwise -> Left "Constant given upper bound that is statically less than given bounds"
        RelocatableCValue{} -> Right bnds
        SymbolCValue{}      -> Right bnds
    AppExpr n a ->
      case a of
        UExt x _ ->
          case testLeq u (typeWidth x) of
            Just LeqProof -> addUpperBound x u bnd bnds
            Nothing ->
              case leqRefl (typeWidth x) of
                LeqProof -> addUpperBound x (typeWidth x) bnd bnds
        Trunc x w ->
            case testLeq u w of
              Just LeqProof -> do
                case testLeq u (typeWidth x) of
                  Just LeqProof -> addUpperBound x u bnd bnds
                  Nothing -> error "addUpperBound invariant broken"
              Nothing -> do
                case testLeq w (typeWidth x) of
                  Just LeqProof -> addUpperBound x w bnd bnds
                  Nothing -> error "addUpperBound invariant broken"
        _ ->
            Right $ bnds { appBoundMap =
                             MapF.insert n (UBVUpperBound u bnd) (appBoundMap bnds)
                         }

-- | Assert a predicate is true/false and update bounds.
--
-- If it returns a new upper bounds, then that may be used.
-- Otherwise, it detects an inconsistency and returns a message
-- explaing why.
assertPred :: ( OrdF (ArchReg arch)
              , HasRepr (ArchReg arch) TypeRepr
              , MemWidth (ArchAddrWidth arch)
              )
           => Value arch ids BoolType -- ^ Value representing predicate
           -> Bool -- ^ Controls whether predicate is true or false
           -> IntraJumpBounds arch ids s -- ^ Current index bounds
           -> Either String (IntraJumpBounds arch ids s)
assertPred (AssignedValue a) isTrue bnds =
  case assignRhs a of
    -- Given x < c), assert x <= c-1
    EvalApp (BVUnsignedLt x (BVValue _ c))
      | isTrue     ->
        if c > 0 then
          addUpperBound (valueExpr bnds x) (typeWidth x) (fromInteger (c-1)) bnds
         else
          Left "x < 0 must be false."
    -- Given not (c < y), assert y <= c
    EvalApp (BVUnsignedLt (BVValue _ c) y)
      | not isTrue -> addUpperBound (valueExpr bnds y) (typeWidth y) (fromInteger c) bnds
    -- Given x <= c, assert x <= c
    EvalApp (BVUnsignedLe x (BVValue _ c))
      | isTrue     -> addUpperBound (valueExpr bnds x) (typeWidth x) (fromInteger c) bnds
    -- Given not (c <= y), assert y <= (c-1)
    EvalApp (BVUnsignedLe (BVValue _ c) y) | not isTrue ->
      if c > 0 then
        addUpperBound (valueExpr bnds y) (typeWidth y) (fromInteger (c-1)) bnds
       else
        Left "0 <= x cannot be false"
    -- Given x && y, assert x, then assert y
    EvalApp (AndApp l r) | isTrue     -> (assertPred l True >=> assertPred r True) bnds
    -- Given not (x || y), assert not x, then assert not y
    EvalApp (OrApp  l r) | not isTrue -> (assertPred l False >=> assertPred r False) bnds
    EvalApp (NotApp p) -> assertPred p (not isTrue) bnds
    _ -> Right bnds
assertPred _ _ bnds = Right bnds

-- | Maps bound expression that have been visited to their location.
type NextBlockState arch ids s = MapF (BoundExpr arch ids s) (BoundLoc (ArchReg arch) )

-- | Return the constraint associated with the given location and expression
-- or nothing if the constraint is the top one and should be stored.
nextStateLocConstraint :: ( MemWidth (ArchAddrWidth arch)
                          , HasRepr (ArchReg arch) TypeRepr
                          , OrdF (ArchReg arch)
                          )
                       => IntraJumpBounds arch ids s
                       -- ^ Bounds at end of this state.
                       -> BoundLoc (ArchReg arch) tp
                          -- ^ Location expression is stored at.
                       -> BoundExpr arch ids s tp
                          -- ^ Expression to infer predicate or.
                       -> State (NextBlockState arch ids s) (Maybe (LocConstraint (ArchReg arch) tp))
nextStateLocConstraint bnds loc e = do
  m <- get
  case MapF.lookup e m of
    Just l ->
      pure $! Just $ EqualValue l
    Nothing -> do
      put $! MapF.insert e loc m
      case exprPred bnds e of
        TopPred -> pure Nothing
        p -> pure $! (Just $! ValueRep p 1)

nextRegConstraint :: ( MemWidth (ArchAddrWidth arch)
                     , HasRepr (ArchReg arch) TypeRepr
                     , OrdF (ArchReg arch)
                     )
                  => IntraJumpBounds arch ids s
                  -- ^ Bounds at end of this state.
                  -> ArchReg arch tp
                  -> Value arch ids tp
                  -> State (NextBlockState arch ids s) (Maybe (LocConstraint (ArchReg arch) tp))
nextRegConstraint bnds r v = nextStateLocConstraint bnds (RegLoc r) (valueExpr bnds v)

nextStackConstraint :: ( MemWidth (ArchAddrWidth arch)
                       , HasRepr (ArchReg arch) TypeRepr
                       , OrdF (ArchReg arch)
                       )
                    => IntraJumpBounds arch ids s
                    -- ^ Bounds at end of this state.
                    -> MemInt (ArchAddrWidth arch)
                    -> MemAnn (BoundExpr arch ids s)
                    -> State (NextBlockState arch ids s) (Maybe (MemAnn (LocConstraint (ArchReg arch))))
nextStackConstraint bnds i (MemAnn repr e) = do
  fmap (MemAnn repr) <$> nextStateLocConstraint bnds (StackOffLoc i repr) e

-- | Bounds for block after jump
nextBlockBounds :: forall arch ids s
                .  RegisterInfo (ArchReg arch)
                => IntraJumpBounds arch ids s
                   -- ^ Bounds at end of this state.
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitJumpBounds arch
nextBlockBounds bnds regs = do
  flip evalState MapF.empty $ do
    regBoundMap <- MapF.traverseMaybeWithKey (nextRegConstraint bnds) (regStateMap regs)
    stackMap    <- Map.traverseMaybeWithKey (nextStackConstraint bnds) (stackExprMap bnds)
    pure $! InitJumpBounds { initialRegBoundMap = regBoundMap
                           , initialStackMap = stackMap
                           }

-- | Return the index bounds after a function call.
postCallBounds :: forall arch ids s
               .  ( RegisterInfo (ArchReg arch)
                  )
               => CallParams (ArchReg arch)
               -> IntraJumpBounds arch ids s
               -> RegState (ArchReg arch) (Value arch ids)
               -> InitJumpBounds arch
postCallBounds params bnds regs = do
  flip evalState MapF.empty $ do
    let filteredRegs = MapF.filterWithKey (\r _ -> preserveReg params r) (regStateMap regs)
    regBoundMap <- MapF.traverseMaybeWithKey (nextRegConstraint bnds) filteredRegs
    let finalStack = stackExprMap bnds
    let filteredStack =
          case valuePred bnds (getBoundValue sp_reg regs) of
            IsStackOffset spOff
              | stackGrowsDown params ->
                  let newOff = spOff + fromInteger (postCallStackDelta params)
                      -- Keep entries whose low address is above new stack offset.
                      p o _v = o >= newOff
                   -- Keep entries at offsets above return address.
                   in Map.filterWithKey p finalStack
              | otherwise ->
                  let newOff :: MemInt (ArchAddrWidth arch)
                      newOff = spOff + fromInteger (postCallStackDelta params)
                      -- Keep entries whose high address is below new stack offset
                      p :: MemInt (ArchAddrWidth arch) -> MemAnn (BoundExpr arch ids s) -> Bool
                      p o (MemAnn r _) = o + fromIntegral (memReprBytes r) <= newOff
                   in Map.filterWithKey p finalStack
            _ -> Map.empty
    stackMap <- Map.traverseMaybeWithKey (nextStackConstraint bnds) filteredStack
    pure $! InitJumpBounds { initialRegBoundMap = regBoundMap
                           , initialStackMap = stackMap
                           }
