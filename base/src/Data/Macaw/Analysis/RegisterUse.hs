{-| This analyzes a Macaw function to compute information about what
information must be available for the code to execute.  It is a key analysis
task needed before deleting unused code.
-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.Analysis.RegisterUse
  ( -- * Exports for function recovery
    registerUse
  , RegisterUseError(..)
    -- ** Input information
  , RegisterUseContext(..)
  , ArchFunType
  , CallRegs(..)
  , PostTermStmtInvariants
  , PostValueMap
  , pvmFind
    -- * Architecture specific summarization
  , ArchTermStmtUsageFn
  , RegisterUseM
  , BlockStartConstraints(..)
  , postCallConstraints
  , BlockUsageSummary(..)
  , RegDependencyMap
  , setRegDep
  , StartInferContext
  , InferState
  , InferValue(..)
  , valueDeps
    -- *** FunPredMap
  , FunPredMap
  , funBlockPreds
    -- ** Inferred information.
  , BlockInvariants
  , biStartConstraints
  , biMemAccessList
  , biPhiLocs
  , biPredPostValues
  , biLocMap
  , biCallFunType
  , LocList(..)
  , MemAccessInfo(..)
  , ValueRegUseDomain(..)
    -- *** Mem Access info
  , StmtIndex
    -- *** Use information
  , biAssignIdUsed
  , biWriteUsed
  ) where

import           Control.Lens
import           Control.Monad.Except
import           Control.Monad.Reader
import           Control.Monad.State.Strict
import           Data.Foldable
import           Data.Kind
import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized
import           Data.Parameterized.Map (MapF)
import qualified Data.Parameterized.Map as MapF
import           Data.Set (Set)
import qualified Data.Set as Set
import           GHC.Stack
import           Prettyprinter

import           Data.Macaw.AbsDomain.StackAnalysis
import           Data.Macaw.CFG
import           Data.Macaw.CFG.DemandSet
  ( DemandContext
  , archFnHasSideEffects
  )
import           Data.Macaw.Discovery.State
import qualified Data.Macaw.Types as M
import           Data.Macaw.Types hiding (Type)
import           Data.Macaw.Utils.Changed
import           Data.Macaw.AbsDomain.CallParams

import           Data.STRef

-------------------------------------------------------------------------------
-- funBlockPreds

-- | A map from each address `l` to the addresses of blocks that may
-- jump to `l`.
type FunPredMap w = Map (MemSegmentOff w) [MemSegmentOff w]

-- | Return the FunPredMap for the discovered block function.
funBlockPreds :: DiscoveryFunInfo arch ids -> FunPredMap (ArchAddrWidth arch)
funBlockPreds info = Map.fromListWith (++)
  [ (next, [addr])
  | b <- Map.elems (info^.parsedBlocks)
    -- Get address of region
  , let addr = pblockAddr b
    -- get the block successors
  , next <- parsedTermSucc (pblockTermStmt b)
  ]

-------------------------------------------------------------------------------
-- RegisterUseError

-- | Errors from register use
data RegisterUseError arch
   = CallStackHeightError !(MemAddr (ArchAddrWidth arch))
   | UnresolvedFunctionTypeError !(ArchSegmentOff arch) !String

instance MemWidth (RegAddrWidth (ArchReg arch)) => Show (RegisterUseError arch) where
  show (CallStackHeightError addr) =
    "Could not resolve concrete stack height for call at "
      ++ show addr
  show (UnresolvedFunctionTypeError addr msg) =
    show addr ++ ": "  ++ msg

-------------------------------------------------------------------------------
-- StackOffset information

-- | This represents a predicate that captures information about the
-- value of a register, stack location, or assignment.
data ValueRegUseDomain arch tp where
  -- | Denotes the value must be the given offset of the stack frame.
  ValueRegUseStackOffset :: !(MemInt (ArchAddrWidth arch))
                         -> ValueRegUseDomain arch (BVType (ArchAddrWidth arch))
  -- | Denotes the value must be the value passed into the function at
  -- the given register.
  FnStartRegister :: !(ArchReg arch tp)
                  -> ValueRegUseDomain arch tp
  -- | This indicates the value is equal to the value stored at the
  -- location.
  --
  -- Note. The location in this is a "representative" location in that
  -- if a location @l@ maps to @RegEqualLoc r@, then all locations
  -- that are equal to this location will map to @RegEqualLoc r@.
  RegEqualLoc :: !(BoundLoc (ArchReg arch) tp)
              -> ValueRegUseDomain arch tp

instance ShowF (ArchReg arch) => Show (ValueRegUseDomain arch tp) where
  showsPrec _ (ValueRegUseStackOffset o) =
    showString "(stack_offset " . shows o . showString ")"
  showsPrec _ (FnStartRegister r) =
    showString "(saved_reg " . showsF r . showString ")"
  showsPrec _ (RegEqualLoc l) =
    showString "(block_loc " . shows (pretty l) . showString ")"

instance ShowF (ArchReg arch) => ShowF (ValueRegUseDomain arch)

instance TestEquality (ArchReg arch) => TestEquality (ValueRegUseDomain arch) where
  testEquality (ValueRegUseStackOffset x) (ValueRegUseStackOffset y) =
    if x == y then Just Refl else Nothing
  testEquality (FnStartRegister x) (FnStartRegister y) =
    testEquality x y
  testEquality (RegEqualLoc x) (RegEqualLoc y) =
    testEquality x y
  testEquality _ _ = Nothing

instance OrdF (ArchReg arch) => OrdF (ValueRegUseDomain arch) where
  compareF (ValueRegUseStackOffset x) (ValueRegUseStackOffset y) =
    fromOrdering (compare x y)
  compareF (ValueRegUseStackOffset _)  _ = LTF
  compareF _ (ValueRegUseStackOffset _)  = GTF

  compareF (FnStartRegister x) (FnStartRegister y) = compareF x y
  compareF (FnStartRegister _) _ = LTF
  compareF _ (FnStartRegister _) = GTF

  compareF (RegEqualLoc x) (RegEqualLoc y) = compareF x y

------------------------------------------------------------------------
-- BlockStartConstraints

-- | This maps r registers and stack offsets at start of block to
-- inferred information about their value.
--
-- If a register or stack location does not appear here, it
-- is implicitly set to itself.
newtype BlockStartConstraints arch =
  BSC { bscLocMap :: LocMap (ArchReg arch) (ValueRegUseDomain arch) }

data TypedPair (key :: k -> Type)  (tp :: k) = TypedPair !(key tp) !(key tp)

instance TestEquality k => TestEquality (TypedPair k) where
  testEquality (TypedPair x1 x2) (TypedPair y1 y2) = do
    Refl <- testEquality x1 y1
    testEquality x2 y2

instance OrdF k => OrdF (TypedPair k) where
  compareF (TypedPair x1 x2) (TypedPair y1 y2) =
    joinOrderingF (compareF x1 y1) (compareF x2 y2)


-- | Return domain for location in constraints
locDomain :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
          => BlockStartConstraints arch
          -> BoundLoc (ArchReg arch) tp
          -> ValueRegUseDomain arch tp
locDomain cns l = fromMaybe (RegEqualLoc l) (locLookup l (bscLocMap cns))

-- | Function for joining constraints on a specific location.
--
-- Used by @joinBlockStartConstraints@ below.
joinValueRegUseDomain :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                      => BlockStartConstraints arch
                         -- ^ New constraints being added to existing one.
                      -> STRef s (LocMap (ArchReg arch) (ValueRegUseDomain arch))
                         -- ^ Map from locations to values that will be used in resulr.
                      -> STRef s (MapF (TypedPair (ValueRegUseDomain arch)) (BoundLoc (ArchReg arch)))
                         -- ^ Cache that maps (old,new) constraints to
                         -- a location that satisfied those
                         -- constraints in old and new constraint set
                         -- respectively.
                      -> BoundLoc (ArchReg arch) tp
                      -> ValueRegUseDomain arch tp
                        -- ^ Old domain for location.
                      -> Changed s ()
joinValueRegUseDomain newCns cnsRef cacheRef l oldDomain = do
  case (oldDomain, locDomain newCns l) of
    (ValueRegUseStackOffset i, ValueRegUseStackOffset j)
      | i == j ->
          changedST $ modifySTRef cnsRef $ nonOverlapLocInsert l oldDomain
    (FnStartRegister rx,  FnStartRegister ry)
      | Just Refl <- testEquality rx ry ->
          changedST $ modifySTRef cnsRef $ nonOverlapLocInsert l oldDomain
    (_, newDomain) -> do
      c <- changedST $ readSTRef cacheRef
      let p = TypedPair oldDomain newDomain
      case MapF.lookup p c of
        Nothing -> do
          -- This is a new class representative.
          -- New class representives imply that there was a change as
          -- the location in the old domain must not have been a free
          -- class rep.
          markChanged True
          changedST $ modifySTRef cacheRef $ MapF.insert p l
        Just prevRep -> do
          -- Mark changed if the old domain was not just a pointer to prevRep.
          case testEquality oldDomain (RegEqualLoc prevRep) of
            Just _ -> pure ()
            Nothing -> markChanged True
          changedST $ modifySTRef cnsRef $ nonOverlapLocInsert l (RegEqualLoc prevRep)

-- | @joinBlockStartConstraints old new@ returns @Nothing@ if @new@
-- implies constraints in @old@, and otherwise a set of constraints
-- @c@ that implies both @new@ and @old@.
joinBlockStartConstraints :: forall s arch
                          .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                          => BlockStartConstraints arch
                          -> BlockStartConstraints arch
                          -> Changed s (BlockStartConstraints arch)
joinBlockStartConstraints (BSC oldCns) newCns = do
  -- Reference to new constraints
  cnsRef <- changedST $ newSTRef locMapEmpty
  -- Cache for recording when we have seen class representatives
  cacheRef <- changedST $ newSTRef MapF.empty

  let regFn :: ArchReg arch tp
            -> ValueRegUseDomain arch tp
            -> Changed s ()
      regFn r d = joinValueRegUseDomain newCns cnsRef cacheRef (RegLoc r) d
  MapF.traverseWithKey_ regFn (locMapRegs oldCns)

  let stackFn :: MemInt (ArchAddrWidth arch)
              -> MemRepr tp
              -> ValueRegUseDomain arch tp
              -> Changed s ()
      stackFn o r d =
        joinValueRegUseDomain newCns cnsRef cacheRef (StackOffLoc o r) d
  memMapTraverseWithKey_ stackFn (locMapStack oldCns)

  changedST $ BSC <$> readSTRef cnsRef

-- | @unionBlockStartConstraints x y@ returns a set of constraints @r@
-- that entails both @x@ and @y@.
unionBlockStartConstraints :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                           => BlockStartConstraints arch
                           -> BlockStartConstraints arch
                           -> BlockStartConstraints arch
unionBlockStartConstraints n o = fromMaybe o (runChanged (joinBlockStartConstraints o n))

-------------------------------------------------------------------------------
-- StmtIndex

-- | Index of a stmt in a block.
type StmtIndex = Int

------------------------------------------------------------------------
-- StartValueExpr

-- | Information about a Macaw value in the invariant inference monad.
data InferValue arch ids tp where
  -- | Value register use domain
  IVDomain :: !(ValueRegUseDomain arch tp)
           -> InferValue arch ids tp
  -- | The value of an assignment.
  IVAssignValue :: !(AssignId ids tp)
                -> InferValue arch ids tp
  -- | A constant
  IVCValue :: !(CValue arch tp) -> InferValue arch ids tp
  -- | Denotes the value written by a conditional write at the given
  -- index if the condition is true, or the value currently stored in
  -- memory if the condition is false.
  --
  -- The MemRepr is the type of the write, and used for comparison.
  IVCondWrite :: !StmtIndex -> !(MemRepr tp) -> InferValue arch ids tp

deriving instance ShowF (ArchReg arch) => Show (InferValue arch ids tp)

instance ShowF (ArchReg arch) => ShowF (InferValue arch ids)

-- | Pattern for stack offset expressions
pattern FrameExpr :: ()
                  => (tp ~ BVType (ArchAddrWidth arch))
                  => MemInt (ArchAddrWidth arch)
                  -> InferValue arch ids tp
pattern FrameExpr o = IVDomain (ValueRegUseStackOffset o)

-- This returns @Just Refl@ if the two expressions denote the same
-- value under the assumptions about the start of the block, and the
-- assumption that non-stack writes do not affect the curent stack
-- frame.
instance TestEquality (ArchReg arch) => TestEquality (InferValue arch ids) where
  testEquality (IVDomain x) (IVDomain y) = testEquality x y
  testEquality (IVAssignValue x) (IVAssignValue y) = testEquality x y
  testEquality (IVCValue x) (IVCValue y) = testEquality x y
  testEquality (IVCondWrite x xtp) (IVCondWrite y ytp) =
    case x == y of
      True ->
        case testEquality xtp ytp of
          Just Refl -> Just Refl
          Nothing -> error "Equal conditional writes with inequal types."
      False -> Nothing
  testEquality _ _ = Nothing

-- Note. The @OrdF@ instance is a total order over @InferValue@.
-- If it returns @EqF@ then it guarantees the two expressions denote
-- the same value under the assumptions about the start of the block,
-- and the assumption that non-stack writes do not affect the curent
-- stack frame.
instance OrdF (ArchReg arch) => OrdF (InferValue arch ids) where
  compareF (IVDomain x) (IVDomain y) = compareF x y
  compareF IVDomain{} _ = LTF
  compareF _ IVDomain{} = GTF

  compareF (IVAssignValue x) (IVAssignValue y) = compareF x y
  compareF IVAssignValue{} _ = LTF
  compareF _ IVAssignValue{} = GTF

  compareF (IVCValue x) (IVCValue y) = compareF x y
  compareF IVCValue{} _ = LTF
  compareF _ IVCValue{} = GTF

  compareF (IVCondWrite x xtp) (IVCondWrite y ytp) =
    case compare x y of
      LT -> LTF
      EQ ->
        case testEquality xtp ytp of
          Just Refl -> EQF
          Nothing -> error "Equal conditional writes with inequal types."
      GT -> GTF

-- | Information about a stack location used in invariant inference.
data InferStackValue arch ids tp where
  -- | The stack location had this value in the initial stack.
  ISVInitValue :: !(ValueRegUseDomain arch tp)
               -> InferStackValue arch ids tp
  -- | The value was written to the stack by a @WriteMem@ instruction
  -- in the current block at the given index, and the value written
  -- had the given inferred value.
  ISVWrite :: !StmtIndex
           -> !(Value arch ids tp)
           -> InferStackValue arch ids tp
  -- | @ISVCondWrite idx c v pv@ denotes the value written to
  -- the stack by a @CondWriteMem@ instruction in the current block
  -- with the given instruction index @idx@, condition @c@, value @v@
  -- and existing stack value @pv@.
  --
  -- The arguments are the index, the Boolean, the value written, and
  -- the value overwritten.
  ISVCondWrite :: !StmtIndex
               -> !(Value arch ids BoolType)
               -> !(Value arch ids tp)
               -> !(InferStackValue arch ids tp)
               -> InferStackValue arch ids tp

------------------------------------------------------------------------
-- StartInfer

-- | Read-only information needed to infer successor start
-- constraints for a lbok.
data StartInferContext arch =
  SIC { sicAddr :: !(MemSegmentOff (ArchAddrWidth arch))
      , sicRegs :: !(MapF (ArchReg arch) (ValueRegUseDomain arch))
        -- ^ Map rep register to rheir initial domain information.
      }

deriving instance (ShowF (ArchReg arch), MemWidth (ArchAddrWidth arch))
      => Show (StartInferContext arch)


-- | Evaluate a value in the context of the start infer state and
-- initial register assignment.
valueToStartExpr :: OrdF (ArchReg arch)
                 => StartInferContext arch
                    -- ^ Initial value of registers
                 -> MapF (AssignId ids) (InferValue arch ids)
                    -- ^ Map from assignments to value.
                 -> Value arch ids tp
                 -> InferValue arch ids tp
valueToStartExpr _ _ (CValue c) = IVCValue c
valueToStartExpr _ am (AssignedValue (Assignment aid _)) =
  MapF.findWithDefault (IVAssignValue aid) aid am
valueToStartExpr ctx _ (Initial r) =
  IVDomain (MapF.findWithDefault (RegEqualLoc (RegLoc r)) r (sicRegs ctx))

inferStackValueToValue :: OrdF (ArchReg arch)
                       => StartInferContext arch
                       -- ^ Initial value of registers
                       -> MapF (AssignId ids) (InferValue arch ids)
                       -- ^ Map from assignments to value.
                       -> InferStackValue arch ids tp
                       -> MemRepr tp
                       -> InferValue arch ids tp
inferStackValueToValue _ _ (ISVInitValue d)   _    = IVDomain d
inferStackValueToValue ctx m (ISVWrite _idx v)  _  = valueToStartExpr ctx m v
inferStackValueToValue _ _ (ISVCondWrite idx _ _ _) repr = IVCondWrite idx repr

-- | Information about a memory access within a block
data MemAccessInfo arch ids
   = -- | The access was not inferred to affect the current frame
     NotFrameAccess
     -- | The access read a frame offset that has not been written to
     -- by the current block.  The domain information is for the value read.
   | forall tp
     . FrameReadInitAccess !(MemInt (ArchAddrWidth arch)) !(ValueRegUseDomain arch tp)
     -- | The access read a frame offset that has been written to by a
     -- previous write or cond-write in this block, and the
     -- instruction had the given index.
   | FrameReadWriteAccess !(MemInt (ArchAddrWidth arch)) !StmtIndex
      -- | The access was a memory read that overlapped, but did not
     -- exactly match a previous write.
   | FrameReadOverlapAccess !(MemInt (ArchAddrWidth arch))
     -- | The access was a write to the current frame.
   | FrameWriteAccess !(MemInt (ArchAddrWidth arch))
     -- | The access was a conditional write to the current frame at the
     -- given offset.  The current
   | forall tp
     . FrameCondWriteAccess !(MemInt (ArchAddrWidth arch))
                            !(MemRepr tp)
                            !(InferStackValue arch ids tp)
     -- | The access was a conditional write to the current frame at the
     -- given offset, and the default value would overlap with a previous
     -- write.
   | FrameCondWriteOverlapAccess !(MemInt (ArchAddrWidth arch))

-- | State tracked to infer block preconditions.
data InferState arch ids =
  SIS { -- | Current stack map.
        --
        -- Note. An uninitialized region at offset @o@ and type @repr@
        -- implicitly is associated with
        -- @ISVInitValue (RegEqualLoc (StackOffLoc o repr))@.
        sisStack :: !(MemMap (MemInt (ArchAddrWidth arch)) (InferStackValue arch ids))
        -- | Maps assignment identifiers to the associated value.
        --
        -- If an assignment id @aid@ is not in this map, then we assume it
        -- is equal to @SAVEqualAssign aid@
      , sisAssignMap :: !(MapF (AssignId ids) (InferValue arch ids))
        -- | Maps apps to the assignment identifier that created it.
      , sisAppCache :: !(MapF (App (InferValue arch ids)) (AssignId ids))
        -- | Offset of current instruction relative to first
        -- instruction in block.
      , sisCurrentInstructionOffset :: !(ArchAddrWord arch)
        -- | Information about memory accesses in reverse order of statement.
        --
        -- There should be exactly one of these for each @ReadMem@,
        -- @CondReadMem@, @WriteMem@ and @CondWriteMem@.
      , sisMemAccessStack :: ![MemAccessInfo arch ids]
      }

-- | Current state of stack.
sisStackLens :: Lens' (InferState arch ids)
                      (MemMap (MemInt (ArchAddrWidth arch)) (InferStackValue arch ids))
sisStackLens = lens sisStack (\s v -> s { sisStack = v })

-- | Maps assignment identifiers to the associated value.
--
-- If an assignment id is not in this map, then we assume it could not
-- be interpreted by the analysis.
sisAssignMapLens :: Lens' (InferState arch ids)
                          (MapF (AssignId ids) (InferValue arch ids))
sisAssignMapLens = lens sisAssignMap (\s v -> s { sisAssignMap = v })

-- | Maps apps to the assignment identifier that created it.
sisAppCacheLens :: Lens' (InferState arch ids)
                         (MapF (App (InferValue arch ids)) (AssignId ids))
sisAppCacheLens = lens sisAppCache (\s v -> s { sisAppCache = v })

-- | Maps apps to the assignment identifier that created it.
sisCurrentInstructionOffsetLens :: Lens' (InferState arch ids) (ArchAddrWord arch)
sisCurrentInstructionOffsetLens =
  lens sisCurrentInstructionOffset (\s v -> s { sisCurrentInstructionOffset = v })

-- | Monad used for inferring start constraints.
--
-- Note. The process of inferring start constraints intentionally does
-- not do stack escape analysis or other
type StartInfer arch ids =
  ReaderT (StartInferContext arch) (State (InferState arch ids))

-- | Set the value associtated with an assignment
setAssignVal :: AssignId ids tp -> InferValue arch ids tp -> StartInfer arch ids ()
setAssignVal aid v = sisAssignMapLens %= MapF.insert aid v

-- | Record the mem access information
addMemAccessInfo :: MemAccessInfo arch ids -> StartInfer arch ids ()
addMemAccessInfo i = seq i $ modify $ \s -> s { sisMemAccessStack = i : sisMemAccessStack s }

processApp :: (OrdF (ArchReg arch), MemWidth (ArchAddrWidth arch))
           => AssignId ids tp
           -> App (Value arch ids) tp
           -> StartInfer arch ids ()
processApp aid app = do
  ctx <- ask
  am <- gets sisAssignMap
  case fmapFC (valueToStartExpr ctx am) app of
    BVAdd _ (FrameExpr o) (IVCValue (BVCValue _ c)) ->
      setAssignVal aid (FrameExpr (o+fromInteger c))
    BVAdd _ (IVCValue (BVCValue _ c)) (FrameExpr o) ->
      setAssignVal aid (FrameExpr (o+fromInteger c))
    BVSub _ (FrameExpr o) (IVCValue (BVCValue _ c)) ->
      setAssignVal aid (FrameExpr (o-fromInteger c))
    appExpr -> do
      c <- gets sisAppCache
      -- Check to see if we have seen an app equivalent to
      -- this one under the invariant assumption.
      case MapF.lookup appExpr c of
        -- If we have not, then record it in the cache for
        -- later.
        Nothing -> do
          sisAppCacheLens %= MapF.insert appExpr aid
        -- If we have seen this app, then we set it equal to previous.
        Just prevId -> do
          setAssignVal aid (IVAssignValue prevId)

-- | Infer constraints from a memory read
inferReadMem :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
               => AssignId ids tp
               -> Value arch ids (BVType (ArchAddrWidth arch))
               -> MemRepr tp
               -> StartInfer arch ids ()
inferReadMem aid addr repr = do
  ctx <- ask
  am <- gets sisAssignMap
  case valueToStartExpr ctx am addr of
    FrameExpr o -> do
      stk <- gets sisStack
      case memMapLookup o repr stk of
        -- Assigned stack read.
        MMLResult sv -> do
          case sv of
            ISVInitValue d -> do
              setAssignVal aid (IVDomain d)
              addMemAccessInfo (FrameReadInitAccess o d)
            ISVWrite writeIdx v -> do
              setAssignVal aid (valueToStartExpr ctx am v)
              addMemAccessInfo (FrameReadWriteAccess o writeIdx)
            ISVCondWrite writeIdx _ _ _ -> do
              setAssignVal aid (IVCondWrite writeIdx repr)
              addMemAccessInfo (FrameReadWriteAccess o writeIdx)
        -- Overlap reads are equal to themselves
        MMLOverlap{} -> do
          addMemAccessInfo (FrameReadOverlapAccess o)
        -- Uninitialized reads are equal to whatever  are equal to themselves.
        MMLNone -> do
          let d = RegEqualLoc (StackOffLoc o repr)
          setAssignVal aid (IVDomain d)
          addMemAccessInfo (FrameReadInitAccess o d)
    -- Non-stack reads are just equal to themselves.
    _ -> addMemAccessInfo NotFrameAccess

-- | Infer constraints from a memory read
inferCondReadMem :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                 => Value arch ids (BVType (ArchAddrWidth arch))
                 -> MemRepr tp
                 -> StartInfer arch ids ()
inferCondReadMem addr repr = do
  ctx <- ask
  s <- gets sisAssignMap
  case valueToStartExpr ctx s addr of
    -- Stack reads need to record the offset.
    FrameExpr o -> do
      stk <- gets sisStack
      case memMapLookup o repr stk of
        -- Assigned stack read.
        MMLResult sv ->
          case sv of
            ISVInitValue d ->
              addMemAccessInfo (FrameReadInitAccess o d)
            ISVWrite writeIdx _v ->
              addMemAccessInfo (FrameReadWriteAccess o writeIdx)
            ISVCondWrite writeIdx _ _ _ ->
              addMemAccessInfo (FrameReadWriteAccess o writeIdx)
        -- Overlap reads are equal to themselves
        MMLOverlap{} -> do
          addMemAccessInfo (FrameReadOverlapAccess o)
        MMLNone -> do
          let d = RegEqualLoc (StackOffLoc o repr)
          addMemAccessInfo (FrameReadInitAccess o d)
    -- Non-stack reads are just equal to themselves.
    _ -> addMemAccessInfo NotFrameAccess

-- | Update start infer statement to reflect statement.
processStmt :: (OrdF (ArchReg arch), MemWidth (ArchAddrWidth arch))
            => StmtIndex
            -> Stmt arch ids
            -> StartInfer arch ids ()
processStmt stmtIdx stmt = do
  case stmt of
    AssignStmt (Assignment aid arhs) ->
      case arhs of
        EvalApp app -> processApp aid app
        -- Assignment equal to itself.
        SetUndefined _ -> pure ()
        ReadMem addr repr -> inferReadMem aid addr repr
        CondReadMem repr _cond addr _falseVal -> inferCondReadMem addr repr
        -- Architecture-specific functions are just equal to themselves.
        EvalArchFn _afn _repr -> pure ()
    WriteMem addr repr val -> do
      ctx <- ask
      s <- gets sisAssignMap
      case valueToStartExpr ctx s addr of
        FrameExpr o -> do
          addMemAccessInfo (FrameWriteAccess o)
          -- Get value of val under current equality constraints.
          sisStackLens %= memMapOverwrite o repr (ISVWrite stmtIdx val)
        -- Do nothing for things that are not stack expressions.
        --
        -- Note.  If @addr@ actually may point to the stack but we end
        -- up in this case, then @sisStack@ will not be properly
        -- updated to reflect real contents, and the value refered
        -- to be subsequent @readMem@ operations may be incorrect.
        --
        -- This is currently unavoidable to fix in this code, and
        -- perhaps can never be fully addressed as we'd basically need
        -- a proof that that the stack could not be overwritten.
        -- However, this will be caught by verification of the
        -- eventual LLVM.
        _ -> addMemAccessInfo NotFrameAccess
    CondWriteMem cond addr repr val -> do
      ctx <- ask
      s <- gets sisAssignMap
      case valueToStartExpr ctx s addr of
        FrameExpr o -> do
          stk <- gets sisStack
          sv <- case memMapLookup o repr stk of
                  MMLResult sv -> do
                    addMemAccessInfo (FrameCondWriteAccess o repr sv)
                    pure sv
                  MMLOverlap{} -> do
                    addMemAccessInfo (FrameCondWriteOverlapAccess o)
                    pure $ ISVInitValue (RegEqualLoc (StackOffLoc o repr))
                  MMLNone -> do
                    let sv = ISVInitValue (RegEqualLoc (StackOffLoc o repr))
                    addMemAccessInfo (FrameCondWriteAccess o repr sv)
                    pure sv
          sisStackLens %= memMapOverwrite o repr (ISVCondWrite stmtIdx cond val sv)
        _ -> do
          addMemAccessInfo NotFrameAccess
    -- Do nothing with instruction start/comment/register update
    InstructionStart o _ ->
      sisCurrentInstructionOffsetLens .= o
    Comment _ -> pure ()
    ArchState{} -> pure ()
    -- For now we assume architecture statement does not modify any
    -- of the locations.
    ExecArchStmt _ -> pure ()

-- | Maps locations to the values to initialize next locations with.
newtype PostValueMap arch ids =
  PVM { _pvmMap :: MapF (BoundLoc (ArchReg arch)) (InferValue arch ids) }

emptyPVM :: PostValueMap arch ids
emptyPVM = PVM MapF.empty

pvmBind :: OrdF (ArchReg arch)
        => BoundLoc (ArchReg arch) tp
        -> InferValue arch ids tp
        -> PostValueMap arch ids
        -> PostValueMap arch ids
pvmBind l v (PVM m) = PVM (MapF.insert l v m)

pvmFind :: OrdF (ArchReg arch)
        => BoundLoc (ArchReg arch) tp
        -> PostValueMap arch ids
        -> InferValue arch ids tp
pvmFind l (PVM m) = MapF.findWithDefault (IVDomain (RegEqualLoc l)) l m

instance ShowF (ArchReg arch) => Show (PostValueMap arch ids) where
  show (PVM m) = show m

ppPVM :: forall arch ids ann . ShowF (ArchReg arch) => PostValueMap arch ids -> Doc ann
ppPVM (PVM m) = vcat $ ppVal <$> MapF.toList m
  where ppVal :: Pair (BoundLoc (ArchReg arch)) (InferValue arch ids) -> Doc ann
        ppVal (Pair l v) = pretty l <+> ":=" <+> viaShow v

type StartInferInfo arch ids =
  ( ParsedBlock arch ids
  , BlockStartConstraints arch
  , InferState arch ids
  , Map (ArchSegmentOff arch) (PostValueMap arch ids)
  )

siiCns :: StartInferInfo arch ids -> BlockStartConstraints arch
siiCns (_,cns,_,_) = cns

type FrontierMap arch = Map (ArchSegmentOff arch) (BlockStartConstraints arch)

data InferNextState arch ids =
  InferNextState { insSeenValues :: !(MapF (InferValue arch ids) (ValueRegUseDomain arch))
                 , insPVM        :: !(PostValueMap arch ids)
                 }

-- | Monad for inferring next state.
type InferNextM arch ids = State (InferNextState arch ids)

runInferNextM :: InferNextM arch ids a -> a
runInferNextM m =
  let s = InferNextState { insSeenValues = MapF.empty
                         , insPVM       = emptyPVM
                         }
   in evalState m s

-- | @memoNextDomain loc expr@ assumes that @expr@ is the value
-- assigned to @loc@ in the next function, and returns the domain to
-- use for that location in the next block start constraints or
-- @Nothing@ if the value is unconstrained.
memoNextDomain :: OrdF (ArchReg arch)
               => BoundLoc (ArchReg arch) tp
               -> InferValue arch ids tp
               -> InferNextM arch ids (Maybe (ValueRegUseDomain arch tp))
memoNextDomain _ (IVDomain d@ValueRegUseStackOffset{}) = pure (Just d)
memoNextDomain _ (IVDomain d@FnStartRegister{}) = pure (Just d)
memoNextDomain loc e = do
  m <- gets insSeenValues
  case MapF.lookup e m of
    Just d -> do
      modify $ \s -> InferNextState { insSeenValues = m
                                    , insPVM = pvmBind loc e (insPVM s)
                                    }
      pure (Just d)
    Nothing -> do
      modify $ \s -> InferNextState { insSeenValues = MapF.insert e (RegEqualLoc loc) m
                                    , insPVM = pvmBind loc e (insPVM s)
                                    }
      pure Nothing

-- | Process terminal registers
addNextConstraints :: forall arch
                   .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                   => (ArchSegmentOff arch -> Maybe (BlockStartConstraints arch))
                   -- ^ Map of previously explored constraints
                   -> ArchSegmentOff arch
                   -- ^ Address to jump to
                   -> BlockStartConstraints arch
                   -- ^ Start constraints at address.
                   -> FrontierMap arch
                   -- ^ New frontier
                   -> FrontierMap arch
addNextConstraints lastMap addr nextCns frontierMap =
  let modifyFrontier :: Maybe (BlockStartConstraints arch)
                     -> Maybe (BlockStartConstraints arch)
      modifyFrontier (Just prevCns) =
        Just (unionBlockStartConstraints nextCns prevCns)
      modifyFrontier Nothing =
        case lastMap addr of
          Nothing -> Just nextCns
          Just prevCns -> runChanged (joinBlockStartConstraints prevCns nextCns)
   in Map.alter modifyFrontier addr frontierMap

-- | Get post value map an dnext constraints for an intra-procedural jump to target.
intraJumpConstraints :: forall arch ids
                     .  OrdF (ArchReg arch)
                     => StartInferContext arch
                     -> InferState arch ids
                     -> RegState (ArchReg arch) (Value arch ids)
                     -- ^ Values assigned to registers at end of blocks.
                     --
                     -- Unassigned registers are considered to be assigned
                     -- arbitrary values.  This is used for modeling calls
                     -- where only some registers are preserved.
                     -> (PostValueMap arch ids, BlockStartConstraints arch)
intraJumpConstraints ctx s regs = runInferNextM $ do
  let intraRegFn :: ArchReg arch tp
                 -> Value arch ids tp
                 -> InferNextM arch ids (Maybe (ValueRegUseDomain arch tp))
      intraRegFn r v = memoNextDomain (RegLoc r) (valueToStartExpr ctx (sisAssignMap s) v)
  regs' <- MapF.traverseMaybeWithKey intraRegFn (regStateMap regs)

  let stackFn :: MemInt (ArchAddrWidth arch)
              -> MemRepr tp
              -> InferStackValue arch ids tp
              -> InferNextM arch ids (Maybe (ValueRegUseDomain arch tp))
      stackFn o repr sv =
        memoNextDomain (StackOffLoc o repr) (inferStackValueToValue ctx (sisAssignMap s) sv repr)
  stk <- memMapTraverseMaybeWithKey stackFn (sisStack s)

  postValMap <- gets insPVM
  let cns = BSC LocMap { locMapRegs = regs'
                       , locMapStack = stk
                       }
  pure (postValMap, cns)

-- | Post call constraints for return address.
postCallConstraints :: forall arch ids
                    .  ArchConstraints arch
                    => CallParams (ArchReg arch)
                       -- ^ Architecture-specific call parameters
                    -> StartInferContext arch
                       -- ^ Context for block invariants inference.
                    -> InferState arch ids
                       -- ^ State for start inference
                    -> RegState (ArchReg arch) (Value arch ids)
                       -- ^ Registers at time of call.
                    -> Either (RegisterUseError arch)
                              (PostValueMap arch ids, BlockStartConstraints arch)
postCallConstraints params ctx s regs =
  runInferNextM $ do
    case valueToStartExpr ctx (sisAssignMap s) (regs^.boundValue sp_reg) of
      FrameExpr spOff -> do
        when (not (stackGrowsDown params)) $
          error "Do not yet support architectures where stack grows up."
        when (postCallStackDelta params < 0) $
          error "Unexpected post call stack delta."
        -- Upper bound is stack offset before call.
        let h = toInteger spOff
        -- Lower bound is stack bound after call.
        let l = h - postCallStackDelta params
        -- Function to update register state.
        let intraRegFn :: ArchReg arch tp
                       -> Value arch ids tp
                       -> InferNextM arch ids (Maybe (ValueRegUseDomain arch tp))
            intraRegFn r v
              | Just Refl <- testEquality r sp_reg = do
                  let spOff' = spOff + fromInteger (postCallStackDelta params)
                  pure (Just (ValueRegUseStackOffset spOff'))
              | preserveReg params r =
                memoNextDomain (RegLoc r) (valueToStartExpr ctx (sisAssignMap s) v)
              | otherwise =
                pure Nothing
        regs' <- MapF.traverseMaybeWithKey intraRegFn (regStateMap regs)

        let stackFn :: MemInt (ArchAddrWidth arch)
                    -> MemRepr tp
                    -> InferStackValue arch ids tp
                    -> InferNextM arch ids (Maybe (ValueRegUseDomain arch tp))
            stackFn o repr sv
              -- Drop the return address pointer
              | l <= toInteger o, toInteger o < h =
                  pure Nothing
              | otherwise =
                -- Otherwise preserve the value.
                  memoNextDomain (StackOffLoc o repr) (inferStackValueToValue ctx (sisAssignMap s) sv repr)

        stk <- memMapTraverseMaybeWithKey stackFn (sisStack s)

        postValMap <- gets insPVM
        let cns = BSC LocMap { locMapRegs = regs'
                             , locMapStack = stk
                             }
        pure $ Right $ (postValMap, cns)
      _ -> pure $ Left (CallStackHeightError (segoffAddr (sicAddr ctx)))

-------------------------------------------------------------------------------
-- DependencySet

-- | This records what assignments and initial value locations are
-- needed to compute a value or execute code in a block with side
-- effects.
data DependencySet (r :: M.Type -> Type) ids =
  DepSet { dsLocSet :: !(Set (Some (BoundLoc r)))
           -- ^ Set of locations that block reads the initial
           -- value of.
         , dsAssignSet :: !(Set (Some (AssignId ids)))
           -- ^ Set of assignments that must be executed.
         , dsWriteStmtIndexSet :: !(Set StmtIndex)
           -- ^ Block start address and index of write statement that
           -- writes a value to the stack that is read later.
         }

ppSet :: (a -> Doc ann) -> Set a -> Doc ann
ppSet f s = encloseSep lbrace rbrace comma (f <$> Set.toList s)

ppSomeAssignId :: Some (AssignId ids) -> Doc ann
ppSomeAssignId (Some aid) = viaShow aid

ppSomeBoundLoc :: MapF.ShowF r => Some (BoundLoc r) -> Doc ann
ppSomeBoundLoc (Some loc) = pretty loc

instance MapF.ShowF r => Pretty (DependencySet r ids) where
  pretty ds =
    vcat [ "Assignments:" <+> ppSet ppSomeAssignId (dsAssignSet ds)
         , "Locations:  " <+> ppSet ppSomeBoundLoc (dsLocSet ds)
         , "Write Stmts:" <+> ppSet pretty (dsWriteStmtIndexSet ds)
         ]

-- | Empty dependency set.
emptyDeps :: DependencySet r ids
emptyDeps =
  DepSet { dsLocSet = Set.empty
         , dsAssignSet = Set.empty
         , dsWriteStmtIndexSet = Set.empty
         }

-- | Dependency set for a single assignment
assignSet :: AssignId ids tp -> DependencySet r ids
assignSet aid =
  DepSet { dsLocSet = Set.empty
         , dsAssignSet = Set.singleton (Some aid)
         , dsWriteStmtIndexSet = Set.empty
         }

-- | Create a dependency set for a single location.
locDepSet :: BoundLoc r tp -> DependencySet r ids
locDepSet l =
  DepSet { dsLocSet = Set.singleton (Some l)
         , dsAssignSet = Set.empty
         , dsWriteStmtIndexSet = Set.empty
         }

-- | @addWriteDep stmtIdx
addWriteDep :: StmtIndex -> DependencySet r ids -> DependencySet r ids
addWriteDep idx s = seq idx $
  s { dsWriteStmtIndexSet = Set.insert idx (dsWriteStmtIndexSet s) }

instance MapF.OrdF r => Semigroup (DependencySet r ids) where
  x <> y = DepSet { dsAssignSet = Set.union (dsAssignSet x) (dsAssignSet y)
                  , dsLocSet = Set.union (dsLocSet x) (dsLocSet y)
                  , dsWriteStmtIndexSet =
                      Set.union (dsWriteStmtIndexSet x) (dsWriteStmtIndexSet y)
                  }

instance MapF.OrdF r => Monoid (DependencySet r ids) where
  mempty = emptyDeps

------------------------------------------------------------------------
-- RegDependencyMap

-- | Map from register to the dependencies for that register.
newtype RegDependencyMap arch ids =
  RDM { rdmMap :: MapF (ArchReg arch) (Const (DependencySet (ArchReg arch) ids)) }

emptyRegDepMap :: RegDependencyMap arch ids
emptyRegDepMap = RDM MapF.empty

instance OrdF (ArchReg arch) => Semigroup (RegDependencyMap arch ids) where
  RDM x <> RDM y = RDM (MapF.union x y)

instance OrdF (ArchReg arch) => Monoid (RegDependencyMap arch ids) where
  mempty = emptyRegDepMap

-- | Set dependency for register
setRegDep :: OrdF (ArchReg arch)
          => ArchReg arch tp
          -> DependencySet (ArchReg arch) ids
          -> RegDependencyMap arch ids
          -> RegDependencyMap arch ids
setRegDep r d (RDM m) = RDM (MapF.insert r (Const d) m)

-- | Create dependencies from map
regDepsFromMap :: (forall tp . a tp -> DependencySet (ArchReg arch) ids)
               -> MapF (ArchReg arch) a
               -> RegDependencyMap arch ids
regDepsFromMap f m = RDM (fmapF (Const . f) m)

------------------------------------------------------------------------
-- BlockUsageSummary

-- | This contains information about a specific block needed to infer
-- which locations and assignments are needed to execute the block
-- along with information about the demands to compute the value of
-- particular locations after the block executes.
data BlockUsageSummary (arch :: Type) ids = BUS
  { blockUsageStartConstraints :: !(BlockStartConstraints arch)
    -- | Offset of start of last instruction processed relative to start of block.
  , blockCurOff :: !(ArchAddrWord arch)
    -- | Information about memory accesses in order of statement.
    --
    -- There should be exactly one of these for each @ReadMem@,
    -- @CondReadMem@, @WriteMem@ and @CondWriteMem@.
  , blockMemAccesses :: ![MemAccessInfo arch ids]
    -- | The contents of the stack at the end of block execution.
  , blockFinalStack :: !(MemMap (MemInt (ArchAddrWidth arch)) (InferStackValue arch ids))
    -- | Dependencies needed to execute statements with side effects.
  ,_blockExecDemands :: !(DependencySet (ArchReg arch) ids)
    -- | Map registers to the dependencies of the values they store.
    --
    -- Defined in block terminator.
  , blockRegDependencies :: !(RegDependencyMap arch ids)
    -- | Map indexes of writes and cond write instructions to their dependency set.
  , blockWriteDependencies :: !(Map StmtIndex (DependencySet (ArchReg arch) ids))
    -- | Maps assignments to their dependencies.
  , assignDeps :: !(Map (Some (AssignId ids)) (DependencySet (ArchReg arch) ids))
    -- | Information about next memory reads.
  , pendingMemAccesses :: ![MemAccessInfo arch ids]
    -- | If this block ends with a call, this has the type of the function called.
    -- Otherwise, the value should be @Nothing@.
  , blockCallFunType :: !(Maybe (ArchFunType arch))
  }

initBlockUsageSummary :: BlockStartConstraints arch
                      -> InferState arch ids
                      -> BlockUsageSummary arch ids
initBlockUsageSummary cns s =
  let a = reverse (sisMemAccessStack s)
   in BUS { blockUsageStartConstraints = cns
          , blockCurOff            = zeroMemWord
          , blockMemAccesses       = a
          , blockFinalStack        = sisStack s
          , _blockExecDemands      = emptyDeps
          , blockRegDependencies   = emptyRegDepMap
          , blockWriteDependencies = Map.empty
          , assignDeps             = Map.empty
          , pendingMemAccesses     = a
          , blockCallFunType = Nothing
          }

-- | Dependencies needed to execute statements with side effects.
blockExecDemands :: Lens' (BlockUsageSummary arch ids) (DependencySet (ArchReg arch) ids)
blockExecDemands = lens _blockExecDemands (\s v -> s { _blockExecDemands = v })

-- | Maps registers to the dependencies needed to compute that
-- register value.
blockRegDependenciesLens :: Lens' (BlockUsageSummary arch ids) (RegDependencyMap arch ids)
blockRegDependenciesLens = lens blockRegDependencies (\s v -> s { blockRegDependencies = v })

-- | Maps stack offsets to the dependencies needed to compute the
-- value stored at that offset.
blockWriteDependencyLens :: Lens' (BlockUsageSummary arch ids)
                                  (Map StmtIndex (DependencySet (ArchReg arch) ids))
blockWriteDependencyLens = lens blockWriteDependencies (\s v -> s { blockWriteDependencies = v })

assignmentCache :: Lens' (BlockUsageSummary arch ids)
                         (Map (Some (AssignId ids)) (DependencySet (ArchReg arch) ids))
assignmentCache = lens assignDeps (\s v -> s { assignDeps = v })

------------------------------------------------------------------------
-- CallRegs

-- | Identifies demand information about a particular call.
data CallRegs (arch :: Type) (ids :: Type) =
  CallRegs { callRegsFnType :: !(ArchFunType arch)
           , callArgValues :: [Some (Value arch ids)]
           , callReturnRegs :: [Some (ArchReg arch)]
           }

------------------------------------------------------------------------
-- RegisterUseContext

type PostTermStmtInvariants arch ids =
  StartInferContext arch
  -> InferState arch ids
  -> ArchTermStmt arch ids
  -> RegState (ArchReg arch) (Value arch ids)
  -> Either (RegisterUseError arch) (PostValueMap arch ids, BlockStartConstraints arch)

type ArchTermStmtUsageFn arch ids
  = ArchTermStmt arch ids
  -> RegState (ArchReg arch) (Value arch ids)
  -> BlockUsageSummary arch ids
  -> Either (RegisterUseError arch) (RegDependencyMap arch ids)

-- | Architecture specific information about the type of function
-- called by inferring call-site information.
--
-- Used to memoize analysis returned by @callDemandFn@.
type family ArchFunType (arch::Type) :: Type

data RegisterUseContext arch
  = RegisterUseContext
    { -- | Set of registers preserved by a call.
      archCallParams :: !(CallParams (ArchReg arch))
      -- | Given a terminal statement and list of registers it returns
      -- Map containing values afterwards.
    , archPostTermStmtInvariants :: !(forall ids . PostTermStmtInvariants arch ids)
      -- | Registers that are saved by calls (excludes rsp)
    , calleeSavedRegisters :: ![Some (ArchReg arch)]
      -- | List of registers that callers may freely change.
    , callScratchRegisters :: ![Some (ArchReg arch)]
      -- ^ The list of registers that are preserved by a function
      -- call.
      --
      -- Note. Should not include stack pointer as thay is
      -- handled differently.
      -- | Return registers demanded by this function
    , returnRegisters :: ![Some (ArchReg arch)]
      -- | Callback function for summarizing register usage of terminal
      -- statements.
    , reguseTermFn :: !(forall ids . ArchTermStmtUsageFn arch ids)
      -- | Given the address of a call instruction and regisdters, this returns the
      -- values read and returned.
    , callDemandFn    :: !(forall ids
                          .  ArchSegmentOff arch
                          -> RegState (ArchReg arch) (Value arch ids)
                          -> Either (RegisterUseError arch) (CallRegs arch ids))
      -- | Information needed to demands of architecture-specific functions.
    , demandContext :: !(DemandContext arch)
    }

-- | Add frontier for an intra-procedural jump that preserves register
-- and stack.
visitIntraJumpTarget :: forall arch ids
                     .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                     => (ArchSegmentOff arch -> Maybe (BlockStartConstraints arch))
                     -> StartInferContext arch
                     -> InferState arch ids
                     -> RegState (ArchReg arch) (Value arch ids)
                     -- ^ Values assigned to registers at end of blocks.
                     --
                     -- Unassigned registers are considered to be assigned
                     -- arbitrary values.  This is used for modeling calls
                     -- where only some registers are preserved.
                     -> (Map (ArchSegmentOff arch) (PostValueMap arch ids), FrontierMap arch)
                     -- ^ Frontier so far
                     -> ArchSegmentOff arch -- ^ Address to jump to
                     -> (Map (ArchSegmentOff arch) (PostValueMap arch ids), FrontierMap arch)
visitIntraJumpTarget lastMap ctx s regs (m,frontierMap) addr =
  let nextCns :: BlockStartConstraints arch
      (postValMap, nextCns) = intraJumpConstraints ctx s regs
   in (Map.insert addr postValMap m, addNextConstraints lastMap addr nextCns frontierMap)

-- | Analyze block to update start constraints on successors and add blocks
-- with changed constraints to frontier.
blockStartConstraints :: ArchConstraints arch
                      => RegisterUseContext arch
                      -> Map (ArchSegmentOff arch) (ParsedBlock arch ids)
                      -- ^ Map from starting addresses to blocks.
                      -> ArchSegmentOff arch
                      -> BlockStartConstraints arch
                      -> Map (ArchSegmentOff arch) (StartInferInfo arch ids)
                      -- ^ Results from last explore map
                      -> FrontierMap arch
                      -- ^ Maps addresses of blocks to explore to the
                      -- starting constraints.
                      -> Except (RegisterUseError arch)
                                (Map (ArchSegmentOff arch) (StartInferInfo arch ids), FrontierMap arch)
blockStartConstraints rctx blockMap addr (BSC cns) lastMap frontierMap = do
  let b = Map.findWithDefault (error "No block") addr blockMap
  let ctx = SIC { sicAddr = addr
                , sicRegs = locMapRegs cns
                }
  let s0  = SIS { sisStack = fmapF ISVInitValue (locMapStack cns)
                , sisAssignMap = MapF.empty
                , sisAppCache  = MapF.empty
                , sisCurrentInstructionOffset = 0
                , sisMemAccessStack = []
                }
  -- Get statements in block
  let stmts = pblockStmts b
  -- Get state from processing all statements
  let s = execState (runReaderT (zipWithM_ processStmt [0..] stmts) ctx) s0
  let lastFn a = if a == addr then Just (BSC cns) else siiCns <$> Map.lookup a lastMap
  case pblockTermStmt b of
    ParsedJump regs next -> do
      let (pvm,frontierMap') = visitIntraJumpTarget lastFn ctx s regs (Map.empty, frontierMap) next
      let m' = Map.insert addr (b, BSC cns, s, pvm) lastMap
      pure $ (m', frontierMap')
    ParsedBranch regs _cond t f -> do
      let (pvm, frontierMap') = foldl' (visitIntraJumpTarget lastFn ctx s regs) (Map.empty, frontierMap) [t,f]
      let m' = Map.insert addr (b, BSC cns, s, pvm) lastMap
      pure $ (m', frontierMap')
    ParsedLookupTable _layout regs _idx lbls -> do
      let (pvm, frontierMap') = foldl' (visitIntraJumpTarget lastFn ctx s regs) (Map.empty, frontierMap) lbls
      let m' = Map.insert addr (b, BSC cns, s, pvm) lastMap
      pure $ (m', frontierMap')
    ParsedCall regs (Just next) -> do
      (postValCns, nextCns) <-
        case postCallConstraints (archCallParams rctx) ctx s regs of
          Left e -> throwError e
          Right r -> pure r
      let m' = Map.insert addr (b, BSC cns, s,  Map.singleton next postValCns) lastMap
      pure (m', addNextConstraints lastFn next nextCns frontierMap)
    -- Tail call
    ParsedCall _ Nothing -> do
      let m' = Map.insert addr (b, BSC cns, s, Map.empty) lastMap
      pure $ (m', frontierMap)
    ParsedReturn _ -> do
      let m' = Map.insert addr (b, BSC cns, s, Map.empty) lastMap
      pure $ (m', frontierMap)
    -- Works like a tail call.
    ParsedArchTermStmt _ _ Nothing -> do
      let m' = Map.insert addr (b, BSC cns, s, Map.empty) lastMap
      pure $ (m', frontierMap)
    ParsedArchTermStmt tstmt regs (Just next) -> do
      case archPostTermStmtInvariants rctx ctx s tstmt regs of
        Left e ->
          throwError e
        Right (postValCns, nextCns) -> do
          let m' = Map.insert addr (b, BSC cns, s, Map.singleton next postValCns) lastMap
          pure (m', addNextConstraints lastFn next nextCns frontierMap)
    ParsedTranslateError _ -> do
      let m' = Map.insert addr (b, BSC cns, s, Map.empty) lastMap
      pure $ (m', frontierMap)
    ClassifyFailure _ _ -> do
      let m' = Map.insert addr (b, BSC cns, s, Map.empty) lastMap
      pure $ (m', frontierMap)
    -- PLT stubs are essentiually tail calls with a non-standard
    -- calling convention.
    PLTStub{} -> do
      let m' = Map.insert addr (b, BSC cns, s, Map.empty) lastMap
      pure $ (m', frontierMap)

-- | Infer start constraints by recursively evaluating blocks
propStartConstraints :: ArchConstraints arch
                     => RegisterUseContext arch
                     -> Map (ArchSegmentOff arch) (ParsedBlock arch ids)
                     -- ^ Map from starting addresses to blocks.
                     -> Map (ArchSegmentOff arch) (StartInferInfo arch ids)
                     -- ^ Map starting address of blocks to information
                     -- about block from last exploration.
                     -> FrontierMap arch
                     -- ^ Maps addresses of blocks to explore to
                     -- the starting constraints.
                     -> Except (RegisterUseError arch)
                               (Map (ArchSegmentOff arch) (StartInferInfo arch ids))
propStartConstraints rctx blockMap lastMap next =
  case Map.minViewWithKey next of
    Nothing -> pure lastMap
    Just ((nextAddr, nextCns), rest) -> do
      (lastMap', next') <- blockStartConstraints rctx blockMap nextAddr nextCns lastMap rest
      propStartConstraints rctx blockMap lastMap' next'

-- | Infer start constraints by recursively evaluating blocks
inferStartConstraints :: forall arch ids
                      .  ArchConstraints arch
                      => RegisterUseContext arch
                      -> Map (ArchSegmentOff arch) (ParsedBlock arch ids)
                      -- ^ Map from starting addresses to blocks.
                      -> ArchSegmentOff arch
                      -- ^ Map starting address of blocks to information
                      -- about block from last exploration.
                      -> Except (RegisterUseError arch)
                                (Map (ArchSegmentOff arch) (StartInferInfo arch ids))
inferStartConstraints rctx blockMap addr = do
  let savedRegs :: [Pair (ArchReg arch) (ValueRegUseDomain arch)]
      savedRegs
        =  [ Pair sp_reg (ValueRegUseStackOffset 0) ]
        ++ [ Pair r (FnStartRegister r) | Some r <- calleeSavedRegisters rctx ]
  let cns = BSC LocMap { locMapRegs = MapF.fromList savedRegs
                       , locMapStack = emptyMemMap
                       }
  propStartConstraints rctx blockMap Map.empty (Map.singleton addr cns)

-- | Pretty print start constraints for debugging purposes.
ppStartConstraints :: forall arch ids ann
                   .  (MemWidth (ArchAddrWidth arch), ShowF (ArchReg arch))
                   => Map (ArchSegmentOff arch) (StartInferInfo arch ids)
                   -> Doc ann
ppStartConstraints m = vcat (pp <$> Map.toList m)
  where pp :: (ArchSegmentOff arch, StartInferInfo arch ids) -> Doc ann
        pp (addr, (_,_,_,pvm)) =
          let pvmEntries = vcat (ppPVMPair <$> Map.toList pvm)
           in vcat [ pretty addr
                   , indent 2 $ vcat ["post-values:", indent 2 pvmEntries] ]
        ppPVMPair :: (ArchSegmentOff arch, PostValueMap arch ids) -> Doc ann
        ppPVMPair (preaddr, pvm) =
          vcat
          [ "to" <+> pretty preaddr <> ":"
          , indent 2 (ppPVM pvm) ]

_ppStartConstraints :: forall arch ids ann
                   .  (MemWidth (ArchAddrWidth arch), ShowF (ArchReg arch))
                   => Map (ArchSegmentOff arch) (StartInferInfo arch ids)
                   -> Doc ann
_ppStartConstraints = ppStartConstraints

------------------------------------------------------------------------
--

-- | This maps each location that could be accessed after a block
-- terminates to the set of values needed to compute the value of the
-- location.
type LocDependencyMap r ids = LocMap r (Const (DependencySet r ids))

-- | Get dependency set for location.
--
-- Note. This code is currently buggy in that it will back propagate
-- stack reads that are partially overwritten.
getLocDependencySet :: (MapF.OrdF r, MemWidth (RegAddrWidth r))
                    => LocDependencyMap r ids
                    -> BoundLoc r tp
                    -> DependencySet r ids
getLocDependencySet srcDepMap l =
  case locLookup l srcDepMap of
    Nothing -> locDepSet l
    Just (Const s) -> s

------------------------------------------------------------------------
-- RegisterUseM

type RegisterUseM arch ids =
  ReaderT (RegisterUseContext arch)
          (StateT (BlockUsageSummary arch ids)
                  (Except (RegisterUseError arch)))

-- ----------------------------------------------------------------------------------------
-- Phase one functions
-- ----------------------------------------------------------------------------------------

domainDeps :: ValueRegUseDomain arch tp -> DependencySet (ArchReg arch) ids
domainDeps (ValueRegUseStackOffset _) = emptyDeps
domainDeps (FnStartRegister _)    = emptyDeps
domainDeps (RegEqualLoc l)        = locDepSet l

-- | Return the register and assignment dependencies needed to
valueDeps :: (HasCallStack, MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
          => BlockStartConstraints arch
          -> Map (Some (AssignId ids)) (DependencySet (ArchReg arch) ids)
          -> Value arch ids tp
          -> DependencySet (ArchReg arch) ids
valueDeps _ _ (CValue _) = emptyDeps
valueDeps cns _ (Initial r) = domainDeps (locDomain cns (RegLoc r))
valueDeps _ m (AssignedValue (Assignment a _)) =
  case Map.lookup (Some a) m of
    Nothing -> error $ "Assignment " ++ show a ++ " is not defined."
    Just r -> r

-- | Record the given dependencies are needed to execute this block.
addDeps :: (HasCallStack, OrdF (ArchReg arch))
        => DependencySet (ArchReg arch) ids
        -> RegisterUseM arch ids ()
addDeps deps = blockExecDemands %= mappend deps

-- | Record the values needed to compute the given value.
demandValue :: (HasCallStack, MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
            => Value arch ids tp
            -> RegisterUseM arch ids ()
demandValue v = do
  cns <- gets blockUsageStartConstraints
  cache <- gets assignDeps
  addDeps (valueDeps cns cache v)

-- | Mark the given register has no dependencies
clearDependencySet :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                   => ArchReg arch tp
                   -> BlockUsageSummary arch ids
                   -> BlockUsageSummary arch ids
clearDependencySet r s =
  s & blockRegDependenciesLens %~ setRegDep r mempty

-- | @recordRegMap m@ record that the values in @regs@ are
-- used to initial registers in the next block and the registers in
-- @l@ can be depended upon.
recordRegMap :: forall arch ids
                    .  (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                    => MapF (ArchReg arch) (Value arch ids)
                    -- ^ Register and assigned values available when block terminates.
                    -> RegisterUseM arch ids ()
recordRegMap m = do
  cns <- gets blockUsageStartConstraints
  cache <- gets assignDeps
  blockRegDependenciesLens .= regDepsFromMap (valueDeps cns cache) m

-- | Set dependencies for an assignment whose right-hand-side must be
-- evaluated for side effects.
requiredAssignDeps :: OrdF (ArchReg arch)
                   => AssignId ids tp
                   -> DependencySet (ArchReg arch) ids
                   -> RegisterUseM arch ids ()
requiredAssignDeps aid deps = do
  addDeps deps
  assignmentCache %= Map.insert (Some aid) mempty

popAccessInfo :: RegisterUseM arch ids (MemAccessInfo arch ids)
popAccessInfo = do
  s <- get
  case pendingMemAccesses s of
    [] -> error "popAccessInfo invalid"
    (i:r) -> do
      put $! s { pendingMemAccesses = r }
      pure i

demandReadMem :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
              => AssignId ids tp
              -> Value arch ids (BVType (ArchAddrWidth arch))
              -> MemRepr tp
              -> RegisterUseM arch ids ()
demandReadMem aid addr _repr = do
  accessInfo <- popAccessInfo
  case accessInfo of
    NotFrameAccess -> do
      -- Mark that this value depends on both aid and any
      -- dependencies needed to compute the address.
      cns <- gets blockUsageStartConstraints
      cache <- gets assignDeps
      let deps = assignSet aid <> valueDeps cns cache addr
      requiredAssignDeps aid deps
    FrameReadInitAccess _o d -> do
      let deps = assignSet aid <> domainDeps d
      assignmentCache %= Map.insert (Some aid) deps
    FrameReadWriteAccess _o writeIdx -> do
      -- Mark that this value depends on aid and any
      -- dependencies needed to compute the value stored at o.
      m <- gets blockWriteDependencies
      let deps = Map.findWithDefault (error "Could not find write index.") writeIdx m
      let allDeps = addWriteDep writeIdx (assignSet aid <> deps)
      assignmentCache %= Map.insert (Some aid) allDeps
    FrameReadOverlapAccess _ -> do
      assignmentCache %= Map.insert (Some aid) (assignSet aid)
    FrameWriteAccess{} ->
      error "Expected read access."
    FrameCondWriteAccess{} ->
      error "Expected read access."
    FrameCondWriteOverlapAccess _ ->
      error "Expected read access."

demandCondReadMem :: (MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                  => AssignId ids tp
                  -> Value arch ids BoolType
                  -> Value arch ids (BVType (ArchAddrWidth arch))
                  -> MemRepr tp
                  -> Value arch ids tp
                  -> RegisterUseM arch ids ()
demandCondReadMem aid cond addr _repr val = do
  accessInfo <- popAccessInfo
  case accessInfo of
    NotFrameAccess -> do
      cns   <- gets blockUsageStartConstraints
      cache <- gets assignDeps
      let deps = mconcat
                    [ assignSet aid
                    , valueDeps cns cache cond
                    , valueDeps cns cache addr
                    , valueDeps cns cache val
                    ]
      requiredAssignDeps aid deps
      addDeps $ assignSet aid
    FrameReadInitAccess _o d -> do
      cns   <- gets blockUsageStartConstraints
      cache <- gets assignDeps
      let deps = mconcat
                 [ assignSet aid
                 , valueDeps cns cache cond
                 , domainDeps d
                 , valueDeps cns cache val
                 ]
      assignmentCache %= Map.insert (Some aid) deps
    FrameReadWriteAccess _o writeIdx -> do
      cns <- gets blockUsageStartConstraints
      cache <- gets assignDeps
      -- Mark that this value depends on aid and any dependencies
      -- needed to compute the value stored at o.
      m <- gets blockWriteDependencies
      let deps = Map.findWithDefault (error "Could not find write index.") writeIdx m
      let allDeps = addWriteDep writeIdx $
                    mconcat [ assignSet aid
                            , valueDeps cns cache cond
                            , deps
                            , valueDeps cns cache val
                            ]
      assignmentCache %= Map.insert (Some aid) allDeps
    FrameReadOverlapAccess _ -> do
      assignmentCache %= Map.insert (Some aid) (assignSet aid)
    FrameWriteAccess{} ->
      error "Expected read access."
    FrameCondWriteAccess{} ->
      error "Expected read access."
    FrameCondWriteOverlapAccess{} ->
      error "Expected read access."

inferStackValueDeps :: (HasCallStack, MemWidth (ArchAddrWidth arch), OrdF (ArchReg arch))
                    => BlockStartConstraints arch
                    -> Map (Some (AssignId ids)) (DependencySet (ArchReg arch) ids)
                    -> InferStackValue arch ids tp
                    -> DependencySet (ArchReg arch) ids
inferStackValueDeps cns amap isv =
  case isv of
    ISVInitValue d -> domainDeps d
    ISVWrite idx v -> addWriteDep idx (valueDeps cns amap v)
    ISVCondWrite idx c v prevVal -> addWriteDep idx $
      mconcat [ valueDeps cns amap c
              , valueDeps cns amap v
              , inferStackValueDeps cns amap prevVal
              ]

demandAssign :: ( MemWidth (ArchAddrWidth arch)
                , OrdF (ArchReg arch)
                , FoldableFC (ArchFn arch)
                )
             => Assignment arch ids tp
             -> RegisterUseM arch ids ()
demandAssign (Assignment aid arhs) =
  case arhs of
    EvalApp app -> do
      cns <- gets blockUsageStartConstraints
      cache <- gets assignDeps
      let deps = foldlFC' (\s v -> mappend s (valueDeps cns cache v)) (assignSet aid) app
      assignmentCache %= Map.insert (Some aid) deps
    SetUndefined{} -> do
      assignmentCache %= Map.insert (Some aid) (assignSet aid)
    ReadMem addr repr -> do
      demandReadMem aid addr repr
    CondReadMem repr c addr val -> do
      demandCondReadMem aid c addr repr val
    EvalArchFn fn _ -> do
      ctx <- asks demandContext
      cns <- gets blockUsageStartConstraints
      cache <- gets assignDeps
      let deps = foldlFC' (\s v -> mappend s (valueDeps cns cache v)) (assignSet aid) fn
      if archFnHasSideEffects ctx fn then do
        requiredAssignDeps aid deps
       else
        assignmentCache %= Map.insert (Some aid) deps

-- | Return values that must be evaluated to execute side effects.
demandStmtValues :: ( HasCallStack
                    , OrdF (ArchReg arch)
                    , MemWidth (ArchAddrWidth arch)
                    , ShowF (ArchReg arch)
                    , FoldableFC (ArchFn arch)
                    , FoldableF (ArchStmt arch)
                    )
                 => StmtIndex -- ^ Index of statement we are processing.
                 -> Stmt arch ids
                    -- ^ Statement we want to demand.
                 -> RegisterUseM arch ids ()
demandStmtValues stmtIdx stmt = do
  case stmt of
   AssignStmt a -> demandAssign a
   WriteMem addr _repr val -> do
     accessInfo <- popAccessInfo
     case accessInfo of
       NotFrameAccess -> do
         demandValue addr
         demandValue val
       FrameReadInitAccess{}    -> error "Expected write access"
       FrameReadWriteAccess{}   -> error "Expected write access"
       FrameReadOverlapAccess{} -> error "Expected write access"
       FrameWriteAccess _o -> do
         cns <- gets blockUsageStartConstraints
         cache <- gets assignDeps
         let valDeps = addWriteDep stmtIdx (valueDeps cns cache val)
         blockWriteDependencyLens %= Map.insert stmtIdx valDeps
       FrameCondWriteAccess{} -> error "Expected write access."
       FrameCondWriteOverlapAccess{} -> error "Expected write access."
   CondWriteMem c addr _repr val -> do
     accessInfo <- popAccessInfo
     case accessInfo of
       NotFrameAccess -> do
         demandValue c
         demandValue addr
         demandValue val
       FrameReadInitAccess{} -> error "Expected conditional write access"
       FrameReadWriteAccess{} -> error "Expected conditional write access"
       FrameReadOverlapAccess{} -> error "Expected conditional write access"
       FrameWriteAccess{} -> error "Expectedf1 conditional write access"
       FrameCondWriteAccess _o _repr sv -> do
         cns <- gets blockUsageStartConstraints
         cache <- gets assignDeps
         let deps = addWriteDep stmtIdx
                      $  valueDeps cns cache c
                      <> inferStackValueDeps cns cache sv
                      <> valueDeps cns cache val
         blockWriteDependencyLens %= Map.insert stmtIdx deps
       FrameCondWriteOverlapAccess _ -> do
         cns <- gets blockUsageStartConstraints
         cache <- gets assignDeps
         let valDeps =
                addWriteDep stmtIdx $
                  valueDeps cns cache c <> valueDeps cns cache val
         blockWriteDependencyLens %= Map.insert stmtIdx valDeps
   InstructionStart off _ -> do
     modify $ \s -> s { blockCurOff = off }
    -- Comment statements have no specific value.
   Comment _ ->
     pure ()
   ExecArchStmt astmt -> do
     traverseF_ demandValue astmt
   ArchState _addr _assn -> do
     pure ()

-- | This function figures out what the block requires (i.e.,
-- addresses that are stored to, and the value stored), along with a
-- map of how demands by successor blocks map back to assignments and
-- registers.
--
-- It returns a summary along with start constraints inferred by
-- blocks that follow this one.
mkBlockUsageSummary :: forall arch ids
               .  ( RegisterInfo (ArchReg arch)
                  , FoldableF (ArchStmt arch)
                  , FoldableFC (ArchFn arch)
                  )
               => RegisterUseContext arch
               -> BlockStartConstraints arch
                  -- ^ Inferred state at start of block
               -> InferState arch ids
                  -- ^ Information inferred from executng block.
               -> ParsedBlock arch ids
                  -- ^ Block
               -> Except (RegisterUseError arch) (BlockUsageSummary arch ids)
mkBlockUsageSummary ctx cns sis blk = do
  flip execStateT (initBlockUsageSummary cns sis) $ flip runReaderT ctx $ do
    let addr = pblockAddr blk
    -- Add demanded values for terminal
    zipWithM_ demandStmtValues [0..] (pblockStmts blk)
    case pblockTermStmt blk of
      ParsedJump regs _tgt -> do
        recordRegMap (regStateMap regs)
      ParsedBranch regs cond _t _f  -> do
        demandValue cond
        recordRegMap (regStateMap regs)
      ParsedLookupTable _layout regs idx _tgts -> do
        demandValue idx
        recordRegMap (regStateMap regs)
      ParsedCall regs _mret -> do
        callFn <- asks callDemandFn
        -- Get function type associated with function
        off <- gets blockCurOff
        let insnAddr =
              let msg = "internal: Expected valid instruction address."
               in fromMaybe (error msg) (incSegmentOff addr (toInteger off))
        demandValue (regs^.boundValue ip_reg)
        ftr <-
          case callFn insnAddr regs of
            Right v -> pure v
            Left e -> throwError e
        -- Demand argument registers
        traverse_ (\(Some v) -> demandValue v) (callArgValues ftr)
        -- Store call register type information
        modify $ \s -> s { blockCallFunType = Just (callRegsFnType ftr) }
        -- Get other things
        cache <- gets assignDeps
        savedRegs <- asks calleeSavedRegisters
        let insReg m (Some r) = setRegDep r (valueDeps cns cache (regs^.boundValue r)) m
        blockRegDependenciesLens %= \m -> foldl' insReg m (Some sp_reg : savedRegs)
        clearedRegs <- asks callScratchRegisters
        let clearReg m (Some r) = setRegDep r mempty m
        blockRegDependenciesLens %= \m -> foldl' clearReg m clearedRegs
        blockRegDependenciesLens %= \m -> foldl' clearReg m (callReturnRegs ftr)
      PLTStub regs _ _ -> do
        traverseF_ demandValue regs
        MapF.traverseWithKey_ (\r _ -> modify $ clearDependencySet r) regs
      ParsedReturn regs -> do
        retRegs <- asks $ returnRegisters
        traverse_ (\(Some r) -> demandValue (regs^.boundValue r)) retRegs

      ParsedArchTermStmt tstmt regs _mnext -> do
        summaryFn <- asks reguseTermFn
        s <- get
        case summaryFn tstmt regs s of
          Left emsg -> throwError emsg
          Right rDeps -> blockRegDependenciesLens .= rDeps
      ParsedTranslateError _ ->
        error "Cannot identify register use in code where translation error occurs"
      ClassifyFailure _ _ ->
        error $ "Classification failed: " ++ show addr

-- | Maps the starting address of a block with the given register type to the value.
type BlockAddrMap r v = Map (MemSegmentOff (RegAddrWidth r)) v

-- | A list of blocks starting addresses and their final location
-- dependency map.
type SrcDependencies r ids =
  [(MemSegmentOff (RegAddrWidth r), LocDependencyMap r ids)]

-- | Maps each block start address to the complete list of blocks that may transition to that block
-- along with the @LocDependencyMap@ for that block.
--
-- This data structure is used to reduce lookups in back-propagation
-- of demands.
type PredProvideMap r ids =
   Map (MemSegmentOff (RegAddrWidth r)) (SrcDependencies r ids)

type NewDemandMap r = BlockAddrMap r (Set (Some (BoundLoc r)))

-- | This takes a list of registers that a block demands that have not
-- been back-propogated, and infers new demands for predecessor
-- registers.
backPropagateOne :: forall r ids
                 .  (MapF.OrdF r, MemWidth (RegAddrWidth r))
                 => BlockAddrMap r (DependencySet r ids)
                 -- ^ State that we are computing fixpoint for.
                 -> NewDemandMap r
                 -- ^ Maps block addresses to the set of register demands we
                 -- have not yet back propagated.
                 -> Set (Some (BoundLoc r))
                 -- ^ Set of new locations the target block depends on
                 -- that we have not yet backpropagate demands to the
                 -- previous block for.

                 -> [( MemSegmentOff (RegAddrWidth r)
                     , LocDependencyMap r ids
                     )]
                 -- ^ Predecessors for the target block and the map from locations
                 -- they provide to the dependency set.
                 -> ( Map (MemSegmentOff (RegAddrWidth r)) (DependencySet r ids)
                    , NewDemandMap r
                    )
backPropagateOne s rest _ [] = (s, rest)
backPropagateOne s rest newLocs ((srcAddr,srcDepMap):predRest) = do
  -- Get dependencies for all new locations that are demanded.
  let allDeps :: DependencySet r ids
      allDeps = mconcat [ getLocDependencySet srcDepMap l | Some l <- Set.toList newLocs ]
  -- Add demands for srcAddr and get existing demands.
  let (mseenRegs, s') =
        Map.insertLookupWithKey (\_ x y -> x <> y) srcAddr allDeps s
  -- Get the difference in demands so that we can propagate further.
  let d = case mseenRegs of
            Nothing -> dsLocSet allDeps
            Just oldDems -> dsLocSet allDeps `Set.difference` dsLocSet oldDems
  -- Update list of additional propagations.
  let rest' | Set.null d = rest
            | otherwise = Map.insertWith Set.union srcAddr d rest
  seq s' $ seq rest' $ backPropagateOne s' rest' newLocs predRest

------------------------------------------------------------------------
-- BlockInvariants

newtype LocList r tp = LL { llValues :: [BoundLoc r tp] }

instance Semigroup (LocList r tp) where
  LL x <> LL y = LL (x++y)

-- | This describes information about a block inferred by
-- register-use.
data BlockInvariants arch ids =
  BI { biUsedAssignSet :: !(Set (Some (AssignId ids)))
       -- | Indices of write and cond-write statements that write to stack
       -- and whose value is later needed to execute the program.
     , biUsedWriteSet  :: !(Set StmtIndex)
       -- | In-order list of memory accesses in block.
     , biMemAccessList :: ![MemAccessInfo arch ids]
       -- | Map from locations to the non-representative locations that are
       -- equal to them.
     , biLocMap :: !(MapF (BoundLoc (ArchReg arch)) (LocList (ArchReg arch)))
       -- | Map predecessors for this block along with map from locations
       -- to phi value
     , biPredPostValues :: !(Map (ArchSegmentOff arch) (PostValueMap arch ids))
       -- | Locations from previous block used to initial phi variables.
     , biPhiLocs :: ![Some (BoundLoc (ArchReg arch))]
       -- | Start constraints for block
     , biStartConstraints :: !(BlockStartConstraints arch)
       -- | If this block ends with a call, this has the type of the function called.
       -- Otherwise, the value should be @Nothing@.
     , biCallFunType :: !(Maybe (ArchFunType arch))
     }

-- | Return true if assignment is needed to execute block.
biAssignIdUsed :: AssignId ids tp -> BlockInvariants arch ids -> Bool
biAssignIdUsed aid inv = Set.member (Some aid) (biUsedAssignSet inv)

-- | Return true if index corresponds to a write of the current stack
-- frame.
biWriteUsed :: StmtIndex -> BlockInvariants arch ids -> Bool
biWriteUsed idx inv = Set.member idx (biUsedWriteSet inv)

-- | This transitively back propagates blocks across
backPropagate :: forall arch ids
              .  (OrdF (ArchReg arch), MemWidth (ArchAddrWidth arch))
              => PredProvideMap (ArchReg arch) ids
              -- ^ Pred provide map computed during summarization.
              -> Map (ArchSegmentOff arch)  (DependencySet (ArchReg arch) ids)
              -> Map (ArchSegmentOff arch) (Set (Some (BoundLoc (ArchReg arch))))
              -- ^ Maps block addresses to the set of locations that
              -- we still need to back propagate demands for.
              -> Map (ArchSegmentOff arch)  (DependencySet (ArchReg arch) ids)
backPropagate predMap depMap new =
  case Map.maxViewWithKey new of
    Nothing -> depMap
    Just ((currAddr, newRegs), rest) ->
      let predAddrs = Map.findWithDefault [] currAddr predMap
          (s', rest') = backPropagateOne depMap rest newRegs predAddrs
       in backPropagate predMap s' rest'

------------------------------------------------------------------------
-- registerUse

-- | Create map from locations to the non-representative locations
-- that are equal to them.
mkDepLocMap :: forall arch
            .  OrdF (ArchReg arch)
            => BlockStartConstraints arch
            -> MapF (BoundLoc (ArchReg arch)) (LocList (ArchReg arch))
mkDepLocMap cns =
  let addNonRep :: MapF (BoundLoc (ArchReg arch)) (LocList (ArchReg arch))
                -> BoundLoc (ArchReg arch) tp
                -> ValueRegUseDomain arch tp
                -> MapF (BoundLoc (ArchReg arch)) (LocList (ArchReg arch))
      addNonRep m l (RegEqualLoc r) = MapF.insertWith (<>) r (LL [l]) m
      addNonRep m _ _ = m
   in foldLocMap addNonRep MapF.empty (bscLocMap cns)

mkBlockInvariants :: forall arch ids
                  .  (HasRepr (ArchReg arch) TypeRepr
                     , OrdF (ArchReg arch)
                     , ShowF (ArchReg arch)
                     , MemWidth (ArchAddrWidth arch)
                     )
                  => FunPredMap (ArchAddrWidth arch)
                  -> (ArchSegmentOff arch
                       -> ArchSegmentOff arch
                       -> PostValueMap arch ids)
                     -- ^ Maps precessor and successor block addresses to the post value from the
                     -- jump from predecessor to successor.
                  -> ArchSegmentOff arch
                     -- ^ Address of thsi block.
                  -> BlockUsageSummary arch ids
                  -> DependencySet (ArchReg arch) ids
                     -- ^ Dependency set for block.
                  -> BlockInvariants arch ids
mkBlockInvariants predMap valueMap addr summary deps =
  let cns   = blockUsageStartConstraints summary
      -- Get addresses of blocks that jump to this block
      preds = Map.findWithDefault [] addr predMap
      -- Maps address of predecessor to the post value for this block.
      predFn predAddr = (predAddr, valueMap predAddr addr)
      predphilist = predFn <$> preds
   in BI { biUsedAssignSet = dsAssignSet deps
         , biUsedWriteSet  = dsWriteStmtIndexSet deps
         , biMemAccessList = blockMemAccesses summary
         , biLocMap = mkDepLocMap cns
         , biPredPostValues = Map.fromList predphilist
         , biPhiLocs = Set.toList (dsLocSet deps)
         , biStartConstraints = cns
         , biCallFunType = blockCallFunType summary
         }

-- | This analyzes a function to determine which registers must b available to
-- the highest index above sp0 that is read or written.
registerUse :: forall arch ids
            .  ArchConstraints arch
            => RegisterUseContext arch
            -> DiscoveryFunInfo arch ids
            -> FunPredMap (ArchAddrWidth arch)
               -- ^ Predecessors for each block in function
            -> Except (RegisterUseError arch)
                      (Map (ArchSegmentOff arch) (BlockInvariants arch ids))
registerUse rctx fun predMap = do
  let blockMap = fun^.parsedBlocks
  -- Infer start constraints
  cnsMap <- inferStartConstraints rctx blockMap (discoveredFunAddr fun)
  -- Infer demand summary for each block
  usageMap <- traverse (\(b, cns,s,_) -> mkBlockUsageSummary rctx cns s b) cnsMap
  -- Back propagate to compute demands
  let bru :: BlockAddrMap (ArchReg arch) (DependencySet (ArchReg arch) ids)
      bru = view blockExecDemands <$> usageMap

  let providePair :: ArchSegmentOff arch -> (ArchSegmentOff arch, LocDependencyMap (ArchReg arch) ids)
      providePair prev = (prev, lm)
        where Just usage = Map.lookup prev usageMap
              cns = blockUsageStartConstraints usage
              cache = assignDeps usage
              lm = LocMap { locMapRegs = rdmMap (blockRegDependencies usage)
                          , locMapStack =
                              fmapF (Const . inferStackValueDeps cns cache)
                                    (blockFinalStack usage)
                          }
  let predProvideMap = fmap (fmap providePair) predMap
  let propMap = backPropagate predProvideMap bru (dsLocSet <$> bru)

  -- Generate final invariants
  let phiValFn :: ArchSegmentOff arch -> ArchSegmentOff arch -> PostValueMap arch ids
      phiValFn predAddr nextAddr =
        case Map.lookup predAddr cnsMap of
          Nothing -> error "Could not find predAddr"
          Just (_,_,_,nextVals) -> Map.findWithDefault emptyPVM nextAddr nextVals
  pure $ Map.intersectionWithKey (mkBlockInvariants predMap phiValFn) usageMap propMap
