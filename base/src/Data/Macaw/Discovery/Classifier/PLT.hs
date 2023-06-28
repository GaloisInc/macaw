{-# LANGUAGE FlexibleContexts #-}
module Data.Macaw.Discovery.Classifier.PLT (
  pltStubClassifier
  ) where

import           Control.Lens ( (^.) )
import           Control.Monad ( when, unless )
import qualified Control.Monad.Reader as CMR
import qualified Data.Foldable as F
import           Data.Monoid ( Any(..) )
import           Data.Parameterized.Classes
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some
import           Data.Parameterized.TraversableF
import           Data.Sequence (Seq)
import qualified Data.Sequence as Seq
import qualified Data.Set as Set

import qualified Data.Macaw.Architecture.Info as Info
import           Data.Macaw.CFG
import qualified Data.Macaw.Discovery.ParsedContents as Parsed

-- | @stripPLTRead assignId prev rest@ looks for a read of @assignId@
-- from the end of @prev@, and if it finds it returns the
-- concatenation of the instruction before the read in @prev@ and
-- @rest@.
--
-- The read may appear before comment and @instructionStart@
-- instructions, but otherwise must be at the end of the instructions
-- in @prev@.
stripPLTRead :: forall arch ids tp
               . ArchConstraints arch
              => AssignId ids tp -- ^ Identifier of write to remove
              -> Seq (Stmt arch ids)
              -> Seq (Stmt arch ids)
              -> Maybe (Seq (Stmt arch ids))
stripPLTRead readId next rest =
  case Seq.viewr next of
    Seq.EmptyR -> Nothing
    prev Seq.:> lastStmt -> do
      let cont = stripPLTRead readId prev (lastStmt Seq.<| rest)
      case lastStmt of
        AssignStmt (Assignment stmtId rhs)
          | Just Refl <- testEquality readId stmtId ->
              Just (prev Seq.>< fmap (dropRefsTo stmtId) rest)
            -- Fail if the read to delete is used in later computations
          | Set.member (Some readId) (foldMapFC refsInValue rhs) ->
              Nothing
          | otherwise ->
            case rhs of
              EvalApp{} -> cont
              SetUndefined{} -> cont
              _ -> Nothing
        InstructionStart{} -> cont
        ArchState{} -> cont
        Comment{} -> cont
        _ -> Nothing
  where
    -- It is possible for later ArchState updates to reference the AssignId of
    -- the AssignStmt that is dropped, so make sure to prune such updates to
    -- avoid referencing the now out-of-scope AssignId.
    dropRefsTo :: AssignId ids tp -> Stmt arch ids -> Stmt arch ids
    dropRefsTo stmtId stmt =
      case stmt of
        ArchState addr updates ->
          ArchState addr $
          MapF.filter (\v -> Some stmtId `Set.notMember` refsInValue v) updates

        -- These Stmts don't contain any Values.
        InstructionStart{} -> stmt
        Comment{}          -> stmt

        -- stripPLTRead will bail out if it encounters any of these forms of
        -- Stmt, so we don't need to consider them.
        AssignStmt{}   -> stmt
        ExecArchStmt{} -> stmt
        CondWriteMem{} -> stmt
        WriteMem{}     -> stmt

removeUnassignedRegs :: forall arch ids
                     .  RegisterInfo (ArchReg arch)
                     => RegState (ArchReg arch) (Value arch ids)
                        -- ^ Initial register values
                     -> RegState (ArchReg arch) (Value arch ids)
                        -- ^ Final register values
                     -> MapF.MapF (ArchReg arch) (Value arch ids)
removeUnassignedRegs initRegs finalRegs =
  let keepReg :: forall tp . ArchReg arch tp -> Value arch ids tp -> Bool
      keepReg r finalVal
         | Just Refl <- testEquality r ip_reg = False
         | Just Refl <- testEquality initVal finalVal = False
         | otherwise = True
        where initVal = initRegs^.boundValue r
   in MapF.filterWithKey keepReg (regStateMap finalRegs)

-- | Return true if any value in structure contains the given
-- identifier.
containsAssignId :: forall t arch ids itp
                 .  FoldableF t
                 => AssignId ids itp
                    -- ^ Forbidden assignment -- may not appear in terms.
                 -> t (Value arch ids)
                 -> Bool
containsAssignId droppedAssign =
  let hasId :: forall tp . Value arch ids tp -> Any
      hasId v = Any (Set.member (Some droppedAssign) (refsInValue v))
   in getAny . foldMapF hasId

-- | A classifier that attempts to recognize PLT stubs
pltStubClassifier :: Info.BlockClassifier arch ids
pltStubClassifier = Info.classifierName "PLT stub" $ do
  bcc <- CMR.ask
  let ctx = Info.classifierParseContext bcc
  let ainfo = Info.pctxArchInfo ctx
  let mem = Info.pctxMemory ctx
  Info.withArchConstraints ainfo $ do

    -- The IP should jump to an address in the .got, so try to compute that.
    AssignedValue (Assignment valId v) <- pure $ Info.classifierFinalRegState bcc ^. boundValue ip_reg
    ReadMem gotVal _repr <- pure $ v
    Just gotSegOff <- pure $ valueAsSegmentOff mem gotVal
    -- The .got contents should point to a relocation to the function
    -- that we will jump to.
    Right chunks <- pure $ segoffContentsAfter gotSegOff
    RelocationRegion r:_ <- pure $ chunks
    -- Check the relocation satisfies all the constraints we expect on PLT strub
    SymbolRelocation sym symVer <- pure $ relocationSym r
    unless (relocationOffset r == 0) $ fail "PLT stub requires 0 offset."
    when (relocationIsRel r) $ fail "PLT stub requires absolute relocation."
    when (toInteger (relocationSize r) /= toInteger (addrWidthReprByteCount (Info.archAddrWidth ainfo))) $ do
      fail $ "PLT stub relocations must match address size."
    when (relocationIsSigned r) $ do
      fail $ "PLT stub relocations must be signed."
    when (relocationEndianness r /= Info.archEndianness ainfo) $ do
      fail $ "PLT relocation endianness must match architecture."
    unless (relocationJumpSlot r) $ do
      fail $ "PLT relocations must be jump slots."
    -- The PLTStub terminator will implicitly read the GOT address, so we remove
    -- it from the list of statements.
    Just strippedStmts <- pure $ stripPLTRead valId (Info.classifierStmts bcc) Seq.empty
    let strippedRegs = removeUnassignedRegs (Info.classifierInitRegState bcc) (Info.classifierFinalRegState bcc)
    when (containsAssignId valId strippedRegs) $ do
      fail $ "PLT IP must be assigned."
    pure $ Parsed.emptyParsedContents { Parsed.parsedNonterm = F.toList strippedStmts
                              , Parsed.parsedTerm  = Parsed.PLTStub strippedRegs gotSegOff (VerSym sym symVer)
                              , Parsed.writtenCodeAddrs = Info.classifierWrittenAddrs bcc
                              , Parsed.intraJumpTargets = []
                              , Parsed.newFunctionAddrs = []
                              }
