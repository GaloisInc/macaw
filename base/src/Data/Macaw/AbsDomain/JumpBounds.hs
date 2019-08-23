{-
This code associates upper bounds with parts of registers and
addresses in the stack.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
module Data.Macaw.AbsDomain.JumpBounds
  ( InitialIndexBounds
  , functionStartBounds
  , joinInitialBounds
  , ppInitialIndexBounds
    -- * Index bounds
  , IndexBounds
  , mkIndexBounds
  , postCallBounds
  , nextBlockBounds
  , assertPred
  , unsignedUpperBound
  , processStmt
  , UpperBound(..)
  ) where

import           Control.Monad.State
import           Data.Functor
import qualified Data.Map.Merge.Strict as Map
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Classes
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.NatRepr
import           Numeric.Natural
import           Text.PrettyPrint.ANSI.Leijen hiding ((<$>))

import           Data.Macaw.AbsDomain.CallParams
import           Data.Macaw.CFG
import           Data.Macaw.Types

------------------------------------------------------------------------
-- Changed

-- | A monad that can be used to record when a value is changed.
type Changed = State Bool

-- | Record the value has changed if the Boolean is true.
markChanged :: Bool -> Changed ()
markChanged b = modify (|| b)

runChanged :: Changed a -> Maybe a
runChanged action =
  case runState action False of
    (r, True)  -> Just r
    (_, False) -> Nothing

------------------------------------------------------------------------
-- UpperBound

-- | An upper bound on a value.
data UpperBound tp where
  -- | @IntegerUpperBound b v@ indicates the low @b@ bits of the value
  -- are at most @v@ when the bitvector is treated as an unsigned
  -- integer.
  UBVUpperBound :: (u <= w) => !(NatRepr u) -> !Natural -> UpperBound (BVType w)

instance Eq (UpperBound tp) where
  UBVUpperBound u x == UBVUpperBound v y =
    case testEquality u v of
      Nothing -> False
      Just Refl -> x == y

instance MapF.EqF UpperBound where
  eqF = (==)

instance Ord (UpperBound tp) where
  compare (UBVUpperBound u x) (UBVUpperBound v y) =
    case compareF u v of
      LTF -> LT
      EQF -> compare x y
      GTF -> GT

deriving instance Show (UpperBound tp)

ppPair :: ShowF r => MapF.Pair r UpperBound -> Doc
ppPair (MapF.Pair k (UBVUpperBound w b)) =
  text (showF k) <> text ":[" <> text (show w) <> text "] <= " <> text (show b)

-- | Print the entries in the list and return all documents.
ppMapFBounds :: ShowF r => MapF r UpperBound -> [Doc]
ppMapFBounds = \m -> ppPair <$> MapF.toList m

------------------------------------------------------------------------
-- InitialIndexBiunds

-- | Bounds for a function as the start of a block.
data InitialIndexBounds r
   = InitialIndexBounds { initialRegBoundMap :: !(MapF r UpperBound)
                          -- ^ Maps each register to the bounds on it.
                        , initialStackOffsets ::
                            !(Map (TypeAp r (BVType (RegAddrWidth r))) (MemInt (RegAddrWidth r)))
                          -- ^ This maps registers values known to be
                          -- at fixed offsets of the stack pointer to
                          -- the offset.
                          --
                          -- All offsets are relative to the function
                          -- entry point.
--                        , stackBounds :: !(Map Integer MemUpperBound)
                        }

ppInitialIndexBounds :: forall r . ShowF r => InitialIndexBounds r -> [Doc]
ppInitialIndexBounds bnds =
  let ppOff :: (TypeAp r (BVType (RegAddrWidth r)), MemInt (RegAddrWidth r)) -> Doc
      ppOff (TypeAp r,o) = text (showF r) <+> text ":= stack_frame" <+> ppAddend o

      ppAddend :: MemInt w -> Doc
      ppAddend o | memIntValue o < 0 = text "-" <+> pretty (negate (toInteger (memIntValue o)))
                 | otherwise = text "+" <+> pretty o
    in ppMapFBounds (initialRegBoundMap bnds)
       ++ fmap ppOff (Map.toList (initialStackOffsets bnds))

instance ShowF r => Pretty (InitialIndexBounds r) where
  pretty = vcat . ppInitialIndexBounds

-- | Bounds at start of function.
functionStartBounds :: RegisterInfo reg => InitialIndexBounds reg
functionStartBounds = InitialIndexBounds { initialRegBoundMap = MapF.empty
                                         , initialStackOffsets = Map.singleton (TypeAp sp_reg) 0
                                         }

-- | Take the union of two index bounds
joinInitialBounds :: forall r
                  .  (MapF.OrdF r)
                  => InitialIndexBounds r
                  -> InitialIndexBounds r
                  -> Maybe (InitialIndexBounds r)
joinInitialBounds old new = runChanged $ do

      -- Mark upper bounds exclusively in old set.
      -- If we have any only-old bounds add mark value as changed.
  let oldF :: MapF r a -> Changed (MapF r a)
      oldF m = markChanged (not (MapF.null m)) $> MapF.empty

      -- How to upper bounds exclusively in new set.
      -- Drop any only-new bounds.
  let newF :: MapF r a -> Changed (MapF r a)
      newF _ = pure MapF.empty

  let combineUpperBounds :: r tp -> UpperBound tp -> UpperBound tp -> Changed (Maybe (UpperBound tp))
      combineUpperBounds _ (UBVUpperBound u x) (UBVUpperBound v y) =
        case testEquality u v of
          Just Refl ->
            markChanged (x < y) $> Just (UBVUpperBound u (max x y))
          Nothing ->
            markChanged True $> Nothing

  resRegBounds    <- MapF.mergeWithKeyM combineUpperBounds  oldF newF (initialRegBoundMap old) (initialRegBoundMap new)

  let combineStackOffsets :: TypeAp r tp
                          -> MemInt (RegAddrWidth r)
                          -> MemInt (RegAddrWidth r)
                          -> Maybe (MemInt (RegAddrWidth r))
      combineStackOffsets _ x y
        | x == y = Just x
        | otherwise = Nothing

  resStackOffsets <-
    Map.mergeA Map.dropMissing Map.dropMissing
               (Map.zipWithMaybeMatched combineStackOffsets)
               (initialStackOffsets old)
               (initialStackOffsets new)

  when (Map.size resStackOffsets /= Map.size (initialStackOffsets old)) $ do
    markChanged True

  pure $! InitialIndexBounds { initialRegBoundMap = resRegBounds
                             , initialStackOffsets = resStackOffsets
                             }

-- | Information about bounds for a particular value within a block.
data IndexBounds reg ids
   = IndexBounds { regBounds           :: !(MapF reg UpperBound)
                   -- ^ Maps register to the upper bound associated with that register.
                 , assignUpperBound   :: !(MapF (AssignId ids) UpperBound)
                 , initRegStackOffsets :: !(Map (TypeAp reg (BVType (RegAddrWidth reg)))
                                                (MemInt (RegAddrWidth reg)))
                   -- ^ Maps initial register values to the stack offset.
                 }

addrTypeRepr :: MemWidth w => TypeRepr (BVType w)
addrTypeRepr = BVTypeRepr w
  where w = addrWidthNatRepr (addrWidthRepr w)

-- | Return the index bounds after a function call.
postCallBounds :: forall arch ids
               .  ( RegisterInfo (ArchReg arch)
                  )
               => CallParams (ArchReg arch)
               -> IndexBounds (ArchReg arch) ids
               -> RegState (ArchReg arch) (Value arch ids)
               -> InitialIndexBounds (ArchReg arch)
postCallBounds params bnds regs =
  -- adjust stack pointer, preserve callee-saved registers
  let tp = addrTypeRepr @(ArchAddrWidth arch)
      mapStackOffset :: ArchReg arch (BVType (ArchAddrWidth arch))
                     -> MemInt (ArchAddrWidth arch)
                     -> Maybe (MemInt (ArchAddrWidth arch))
      mapStackOffset r o
        | Just Refl <- testEquality r sp_reg =
            Just $! o + fromInteger (postCallStackDelta params)
        | preserveReg params r = Just o
        | otherwise = Nothing
   in InitialIndexBounds { initialRegBoundMap = MapF.empty
                         , initialStackOffsets = Map.fromAscList
                             [ (TypeAp r, o)
                             | MapF.Pair r v <- MapF.toList (regStateMap regs)
                             , Refl <- maybeToList $ testEquality tp (typeRepr r)
                             , o <- maybeToList $ mapStackOffset r =<< stackOffset bnds v
                             ]
                         }

instance ShowF reg => Pretty (IndexBounds reg idx) where
  pretty bnds =
    vcat $ ppMapFBounds (regBounds bnds)
        ++ ppMapFBounds (assignUpperBound bnds)

-- | Create index bounds from initial index bounds.
mkIndexBounds :: InitialIndexBounds reg -> IndexBounds reg ids
mkIndexBounds i = IndexBounds { regBounds = initialRegBoundMap i
                              , assignUpperBound = MapF.empty
                              , initRegStackOffsets = initialStackOffsets i
                              }

------------------------------------------------------------------------
-- Operations

{-
memWrite :: ( RegisterInfo (ArchReg arch)
            , MemWidth (ArchAddrWidth arch)
            , HasCallStack
            )
         => BVValue arch ids (ArchAddrWidth arch)
         -- ^ Address that we are writing to.
         -> MemRepr tp
         -- ^ Information about how value should be represented in memory.
         -> Value arch ids tp
         -- ^ Value to write to memory
         -> IndexBounds (ArchReg arch) ids
         -- ^ Current processor state.
         -> IndexBounds (ArchReg arch) ids
memWrite _a _memRepr _v r = r


-- | Update the processor state with a potential memory write.
condMemWrite :: ( RegisterInfo (ArchReg arch)
                , MemWidth (ArchAddrWidth arch)
                , HasCallStack
                )
             => Value arch ids BoolType
             -- ^ Condition we are splitting on
             -> Value arch ids (BVType (RegAddrWidth r))
             -- ^ Address that we are writing to.
             -> MemRepr tp
             -- ^ Information about how value should be represented in memory.
             -> Value arch ids tp
             -- ^ Value to write to memory
             -> IndexBounds (ArchReg arch)ids
             -- ^ Current processor state.
             -> IndexBounds (ArchReg arch) ids
condMemWrite _cond _a _memRepr _v r = r
-}

-- | Lookup an upper bound or return analysis for why it is not defined.
unsignedUpperBound :: ( MapF.OrdF (ArchReg arch)
                      , MapF.ShowF (ArchReg arch)
                      , RegisterInfo (ArchReg arch)
                      )
                  => IndexBounds (ArchReg arch) ids
                  -> Value arch ids tp
                  -> Either String (UpperBound tp)
unsignedUpperBound bnds v =
  case v of
    BoolValue _ -> Left "Boolean values do not have bounds."
    BVValue w i -> Right $! UBVUpperBound w (fromInteger i)
    RelocatableValue{} ->
      Left "Relocatable values do not have bounds."
    SymbolValue{} ->
      Left "Symbol values do not have bounds."
    AssignedValue a ->
      case MapF.lookup (assignId a) (assignUpperBound bnds) of
        Just bnd -> Right bnd
        Nothing ->
          case assignRhs a of
            EvalApp (BVAnd _ x y) -> do
              case (unsignedUpperBound bnds x,  unsignedUpperBound bnds y) of
                (Right (UBVUpperBound xw xb), Right (UBVUpperBound yw yb))
                  | Just Refl <- testEquality xw yw ->
                    Right (UBVUpperBound xw (min xb yb))
                (Right xb, _) -> Right xb
                (Left{}, yb)       -> yb
            EvalApp (SExt x w) -> do
              UBVUpperBound u b <- unsignedUpperBound bnds x
              case testLeq u w of
                Just LeqProof -> pure $! UBVUpperBound u b
                Nothing -> error "unsignedUpperBound given bad width"
            EvalApp (UExt x w) -> do
              UBVUpperBound u r <- unsignedUpperBound bnds x
              -- If bound is full width, then we can keep it, otherwise we only have subset.
              case testEquality u (typeWidth x) of
                Just Refl -> pure $! UBVUpperBound w r
                Nothing ->
                  case testLeq u w of
                    Just LeqProof -> pure $! UBVUpperBound u r
                    Nothing -> error "unsignedUpperBound given bad width"
            EvalApp (Trunc x w) -> do
              UBVUpperBound u xr <- unsignedUpperBound bnds x
              case testLeq u w of
                Just LeqProof -> do
                  pure $! UBVUpperBound u xr
                Nothing -> do
                  pure $! UBVUpperBound w (min xr (fromInteger (maxUnsigned w)))
            _ -> Left $ "Could not find upper bounds for " ++ show v ++ "."
    Initial r ->
      case MapF.lookup r (regBounds bnds) of
        Just bnd -> Right bnd
        Nothing -> Left $ "No upper bounds for " ++ showF r ++ "."

-- | This returns an offset if we can statically infer that the value
-- must be an offset of the stack.
stackOffset :: ( OrdF (ArchReg arch)
               , MemWidth (ArchAddrWidth arch)
               )
            => IndexBounds (ArchReg arch) ids
            -> Value arch ids (BVType (ArchAddrWidth arch))
            -> Maybe (MemInt (ArchAddrWidth arch))
stackOffset bnds v =
  case v of
    Initial r -> Map.lookup (TypeAp r) (initRegStackOffsets bnds)
    CValue _ -> Nothing
    AssignedValue a ->
      case assignRhs a of
        EvalApp (BVAdd _ x y)
          | BVValue _ i <- x
          , Just j <- stackOffset bnds y -> do
              Just $! fromInteger i+j
          | BVValue _ j <- y
          , Just i <- stackOffset bnds x -> do
              Just $! i+fromInteger j
        EvalApp (BVSub _ x y)
          | BVValue _ j <- y
          , Just i <- stackOffset bnds x -> do
              Just $! i-fromInteger j
        _ -> Nothing

eitherToMaybe :: Either a b -> Maybe b
eitherToMaybe (Right v) = Just v
eitherToMaybe Left{}    = Nothing

-- | Bounds for block after jump
nextBlockBounds :: forall arch ids
                .  RegisterInfo (ArchReg arch)
                => IndexBounds (ArchReg arch) ids
                   -- ^ Index bounds at end of this state.
                -> RegState (ArchReg arch) (Value arch ids)
                   -- ^ Register values at start of next state.
                -> InitialIndexBounds (ArchReg arch)
nextBlockBounds bnds regs =
  let newRegMap = regStateMap regs
      tp = addrTypeRepr @(ArchAddrWidth arch)
   in InitialIndexBounds { initialRegBoundMap =
                             MapF.mapMaybe (eitherToMaybe . unsignedUpperBound bnds) newRegMap
                         , initialStackOffsets  =
                             Map.fromAscList
                               [ (TypeAp r, o)
                               | MapF.Pair r v <- MapF.toAscList newRegMap
                               , Refl <- maybeToList $ testEquality (typeRepr r) tp
                               , o <- maybeToList (stackOffset bnds v)
                               ]
                         }


-- | Given a statement this modifies the processor state based on the statement.
processStmt :: IndexBounds (ArchReg arch) ids
            -> Stmt arch ids
            -> IndexBounds (ArchReg arch) ids
processStmt bnds _s = bnds


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
                 )
               => BVValue arch ids w
                 -- ^ Value we are adding upper bound for.
               -> NatRepr u
                  -- ^ Restrict upper bound to only `u` bits.
               -> Natural
               -- ^ Upper bound as an unsigned number
               -> IndexBounds (ArchReg arch) ids
                 -- ^ Current bounds.
               -> Either String (IndexBounds (ArchReg arch) ids)
addUpperBound v u bnd bnds
    -- Do nothing if upper bounds equals or exceeds function
  | bnd >= fromInteger (maxUnsigned (typeWidth v)) = Right bnds
  | otherwise =
  case v of
    BVValue _ c | c <= toInteger bnd -> Right bnds
                | otherwise -> Left "Constant given upper bound that is statically less than given bounds"
    RelocatableValue{} -> Right bnds
    SymbolValue{}      -> Right bnds
    AssignedValue a ->
      case assignRhs a of
        EvalApp (UExt x _) ->
          case testLeq u (typeWidth x) of
            Just LeqProof -> addUpperBound x u bnd bnds
            Nothing ->
              case leqRefl (typeWidth x) of
                LeqProof -> addUpperBound x (typeWidth x) bnd bnds
        EvalApp (Trunc x w) ->
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
          Right $ bnds { assignUpperBound =
                           MapF.insertWith min (assignId a) (UBVUpperBound u bnd)
                             (assignUpperBound bnds)
                       }
    Initial r ->
      Right $ bnds { regBounds = MapF.insertWith min r (UBVUpperBound u bnd) (regBounds bnds) }

-- | Assert a predicate is true/false and update bounds.
--
-- If it returns a new upper bounds, then that may be used.
-- Otherwise, it detects an inconsistency and returns a message
-- explaing why.
assertPred :: ( OrdF (ArchReg arch)
              , HasRepr (ArchReg arch) TypeRepr
              )
           => Value arch ids BoolType -- ^ Value represnting predicate
           -> Bool -- ^ Controls whether predicate is true or false
           -> IndexBounds (ArchReg arch) ids -- ^ Current index bounds
           -> Either String (IndexBounds (ArchReg arch) ids)
assertPred (AssignedValue a) isTrue bnds =
  case assignRhs a of
    -- Given x < c), assert x <= c-1
    EvalApp (BVUnsignedLt x (BVValue _ c))
      | isTrue     ->
        if c > 0 then
          addUpperBound x (typeWidth x) (fromInteger (c-1)) bnds
         else
          Left "x < 0 must be false."
    -- Given not (c < y), assert y <= c
    EvalApp (BVUnsignedLt (BVValue _ c) y)
      | not isTrue -> addUpperBound y (typeWidth y) (fromInteger c) bnds
    -- Given x <= c, assert x <= c
    EvalApp (BVUnsignedLe x (BVValue _ c))
      | isTrue     -> addUpperBound x (typeWidth x) (fromInteger c) bnds
    -- Given not (c <= y), assert y <= (c-1)
    EvalApp (BVUnsignedLe (BVValue _ c) y) | not isTrue ->
      if c > 0 then
        addUpperBound y (typeWidth y) (fromInteger (c-1)) bnds
       else
        Left "0 <= x cannot be false"
    -- Given x && y, assert x, then assert y
    EvalApp (AndApp l r) | isTrue     -> (assertPred l True >=> assertPred r True) bnds
    -- Given not (x || y), assert not x, then assert not y
    EvalApp (OrApp  l r) | not isTrue -> (assertPred l False >=> assertPred r False) bnds
    EvalApp (NotApp p) -> assertPred p (not isTrue) bnds
    _ -> Right bnds
assertPred _ _ bnds = Right bnds
