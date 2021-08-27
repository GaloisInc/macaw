{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE NondecreasingIndentation #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternGuards #-}
{-# LANGUAGE PatternSynonyms #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE MultiParamTypeClasses #-}

-- | The macaw-symbolic library translates Macaw functions (or blocks) into
-- Crucible CFGs for further analysis or symbolic execution.
--
-- This module (Data.Macaw.Symbolic) provides the entire user-facing API of the
-- library.  There are two main portions of the API:
--
-- 1. Translation of Macaw IR into Crucible CFGs
-- 2. Symbolic execution of Crucible CFGs generated from Macaw
--
-- There are examples of each use case in the relevant sections of the haddocks.
--
-- There is an additional module provided as an example of the memory
-- translation API (see the 'MO.GlobalMap' type) in Data.Macaw.Symbolic.Memory.
-- It is not the only way to use the API, but it should suffice for a wide
-- variety of use cases.  Moreover, it is complicated enough that it would be
-- best to avoid duplicating it unless necessary.
--
-- There is also a separate module (Data.Macaw.Symbolic.Backend) that exports
-- definitions required for implementing architecture-specific backends, but not
-- useful to general client code.
--
-- There are a few things to note about the translation performed by macaw-symbolic:
--
-- * Memory operations are translated into operations over the LLVM memory model
--   provided by crucible-llvm.  This memory model makes some assumptions that
--   do not necessarily hold for all machine code programs, but that do hold for
--   (correct) C and C++ programs.  The current state of memory is held in a
--   Crucible global value that is modified by all code.
--
-- * Each function takes a single argument (the full set of machine registers)
--   and returns a single value (the full set of machine registers reflecting
--   any modifications)
module Data.Macaw.Symbolic
  ( GenArchInfo(..)
  , ArchInfo
  , GenArchVals(..)
  , ArchVals
  , archVals
  , IsMemoryModel(..)
  , LLVMMemory
  , SB.MacawArchEvalFn
    -- * Translation of Macaw IR into Crucible
    -- $translationNaming
    -- $translationExample
    -- ** Translating entire functions
  , mkFunCFG
  , mkFunRegCFG
    -- ** Translating arbitrary collections of blocks
  , mkBlocksRegCFG
  , mkBlocksCFG
  , addBlocksCFG
  , mkCrucRegCFG
    -- ** Translating individual blocks
  , mkParsedBlockRegCFG
  , mkParsedBlockCFG
    -- ** Translating block paths
  , mkBlockPathRegCFG
  , mkBlockPathCFG
    -- * Translating slices of CFGs
  , mkBlockSliceRegCFG
  , mkBlockSliceCFG
  , MacawBlockEndCase(..)
  , MacawBlockEndType
  , MacawBlockEnd(..)
  , isBlockEndCase
  , blockEndCase
  , blockEndReturn
  , initBlockEnd
    -- ** Post-processing helpers
  , toCoreCFG
    -- ** Translation-related types
    -- $translationHelpers
  , CG.MacawSymbolicArchFunctions
  , CG.crucGenRegAssignment
  , CG.crucGenArchRegName
  , CG.MemSegmentMap
    -- * Inspecting and typing generated terms
  , CG.ArchRegStruct
  , CG.MacawCrucibleRegTypes
  , CG.crucArchRegTypes
  , PS.ToCrucibleType
  , PS.ToCrucibleFloatInfo
  , PS.FromCrucibleFloatInfo
  , PS.floatInfoToCrucible
  , PS.floatInfoFromCrucible
  , PS.ArchRegContext
  , PS.macawAssignToCruc
  , PS.macawAssignToCrucM
  , CG.MacawFunctionArgs
  , CG.MacawFunctionResult
  , PS.typeToCrucible
  , PS.typeCtxToCrucible
  , PS.MacawCrucibleValue(..)
  , PS.CtxToCrucibleType
  -- ** The Macaw extension to Crucible
  , CG.MacawExt
  , CG.MacawExprExtension(..)
  , evalMacawExprExtension
  , CG.MacawStmtExtension(..)
  , CG.MacawOverflowOp(..)
    -- * Simulating generated Crucible CFGs
    -- $simulationNotes
    -- $simulationExample
  , SymArchConstraints
  , macawExtensions
  , PtrOp
  , ptrOp
  , isValidPtr
  , mkUndefinedBool
  , MO.GlobalMap
  , MO.LookupFunctionHandle(..)
  , MO.LookupSyscallHandle(..)
  , MO.MacawSimulatorState(..)
  , MkGlobalPointerValidityAssertion
  , PointerUse(..)
  , PointerUseTag(..)
  , pointerUseLocation
  , pointerUseTag
    -- * Simplified entry points
  , runCodeBlock
  ) where

import           GHC.TypeLits
import           GHC.Exts

import           Control.Lens ((^.))
import           Control.Monad
import           Control.Monad.State
import qualified Data.BitVector.Sized as BV
import qualified Data.Foldable as F
import qualified Data.Map.Strict as Map
import           Data.Proxy
import           Data.Maybe
import           Data.Parameterized.Context (EmptyCtx, (::>), pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce ( NonceGenerator, newIONonceGenerator )
import           Data.Parameterized.Some ( Some(Some) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Set as S
import qualified Data.Text as T

import qualified What4.FunctionName as C
import           What4.Interface
import           What4.Partial
import qualified What4.Utils.StringLiteral as C
import qualified What4.ProgramLoc as WPL

import qualified Lang.Crucible.Analysis.Postdom as C
import           Lang.Crucible.Backend
import qualified Lang.Crucible.CFG.Core as C
import qualified Lang.Crucible.CFG.Expr as C
import qualified Lang.Crucible.CFG.Reg as CR
import qualified Lang.Crucible.CFG.SSAConversion as C
import qualified Lang.Crucible.FunctionHandle as C

import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.GlobalState as C

import qualified Lang.Crucible.Utils.MuxTree as C

import           System.IO (stdout)

import qualified Lang.Crucible.LLVM.MemModel as MM
import           Lang.Crucible.LLVM.Intrinsics (llvmIntrinsicTypes)

import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Types as M

import qualified Data.Macaw.Symbolic.Backend as SB
import           Data.Macaw.Symbolic.Bitcast ( doBitcast )
import qualified Data.Macaw.Symbolic.CrucGen as CG
import           Data.Macaw.Symbolic.CrucGen hiding (bvLit)
import           Data.Macaw.Symbolic.PersistentState as PS
import           Data.Macaw.Symbolic.MemOps as MO

-- | A class to capture the architecture-specific information required to
-- translate macaw IR into Crucible.
--
-- It is intended to provide a single interface for obtaining the information
-- necessary to perform the translation (i.e., if you implement an
-- architecture-specific backend for macaw-symbolic, make your architecture an
-- instance of this class).
--
-- The return value is a 'Maybe' so that architectures that do not yet support
-- the translation can return 'Nothing', while still allowing fully generic client
-- code to be written in terms of this class constraint.
--
-- The 'mem' type parameter indicates the memory model to be used for translation.
-- The type alias 'ArchInfo' specializes this class to the llvm memory model
-- using the 'LLVMMemory' type tag.
class GenArchInfo mem arch where
  genArchVals :: proxy mem -> proxy' arch -> Maybe (GenArchVals mem arch)

type ArchInfo arch = GenArchInfo LLVMMemory arch

archVals
  :: ArchInfo arch
  => proxy arch
  -> Maybe (ArchVals arch)
archVals p = genArchVals (Proxy @LLVMMemory) p

data LLVMMemory

class IsMemoryModel mem where
  type MemModelType mem arch :: C.CrucibleType
  type MemModelConstraint mem sym :: Constraint

instance IsMemoryModel LLVMMemory where
  type MemModelType LLVMMemory arch = MM.Mem
  type MemModelConstraint LLVMMemory sym = MM.HasLLVMAnn sym

-- | The information to support use of macaw-symbolic for a given architecture
data GenArchVals mem arch = GenArchVals
  { archFunctions :: MacawSymbolicArchFunctions arch
  -- ^ This is the set of functions used by the translator, and is passed as the
  -- first argument to the translation functions (e.g., 'mkBlocksCFG').
  , withArchEval
      :: forall a m sym
       . (IsSymInterface sym, IsMemoryModel mem, MemModelConstraint mem sym, MonadIO m)
      => sym
      -> (SB.MacawArchEvalFn sym (MemModelType mem arch) arch -> m a)
      -> m a
  -- ^ This function provides a context with a callback that gives access to the
  -- set of architecture-specific function evaluators ('MacawArchEvalFn'), which
  -- is a required argument for 'macawExtensions'.
  , withArchConstraints :: forall a . (SymArchConstraints arch => a) -> a
  -- ^ This function captures the constraints necessary to invoke the symbolic
  -- simulator on a Crucible CFG generated from macaw.
  , lookupReg
      :: forall sym tp
       . (SymArchConstraints arch, IsSymInterface sym)
      => C.RegEntry sym (CG.ArchRegStruct arch)
      -> M.ArchReg arch tp
      -> C.RegEntry sym (PS.ToCrucibleType tp)
  , updateReg
      :: forall sym tp
       . (SymArchConstraints arch, IsSymInterface sym)
      => C.RegEntry sym (CG.ArchRegStruct arch)
      -> M.ArchReg arch tp
      -> C.RegValue sym (PS.ToCrucibleType tp)
      -> C.RegEntry sym (CG.ArchRegStruct arch)
  }

type ArchVals arch = GenArchVals LLVMMemory arch

-- | All of the constraints on an architecture necessary for translating and
-- simulating macaw functions in Crucible
type SymArchConstraints arch =
  ( M.ArchConstraints arch
  , M.RegisterInfo (M.ArchReg arch)
  , M.HasRepr (M.ArchReg arch) M.TypeRepr
  , M.MemWidth (M.ArchAddrWidth arch)
  , KnownNat (M.ArchAddrWidth arch)
  , M.PrettyF (M.ArchReg arch)
  , Show (M.ArchReg arch (M.BVType (M.ArchAddrWidth arch)))
  , ArchInfo arch
  , FC.TraversableFC (CG.MacawArchStmtExtension arch)
  , C.TypeApp (CG.MacawArchStmtExtension arch)
  , C.PrettyApp (CG.MacawArchStmtExtension arch)
  )

-- * Translation functions

-- | Create a Crucible registerized CFG from a list of blocks
--
-- Useful as an alternative to 'mkCrucCFG' if post-processing is
-- desired (as this is easier to do with the registerized form); use
-- 'toCoreCFG' to finish.
mkCrucRegCFG :: forall arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible architecture-specific functions.
            -> C.HandleAllocator
               -- ^ Handle allocator to make function handles
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> (forall s. MacawMonad arch ids s (CR.Label s, [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]))
                -- ^ Action to run
            -> IO (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkCrucRegCFG archFns halloc nm action = do
  let crucRegTypes = crucArchRegTypes archFns
  let macawStructRepr = C.StructRepr crucRegTypes
  let argTypes = Empty :> macawStructRepr
  h <- C.mkHandle' halloc nm argTypes macawStructRepr
  Some (ng :: NonceGenerator IO s) <- newIONonceGenerator
  let ps0 = initCrucPersistentState ng
  blockRes <- runMacawMonad ps0 action
  (entry, blks) <-
    case blockRes of
      (Left err, _) -> fail err
      (Right pair, _fs)  -> pure pair

  -- Create control flow graph
  let rg :: CR.CFG (MacawExt arch) s (MacawFunctionArgs arch) (MacawFunctionResult arch)
      rg = CR.CFG { CR.cfgHandle = h
                  , CR.cfgEntryLabel = entry
                  , CR.cfgBlocks = blks
                  }
  pure $ CR.SomeCFG rg

-- | Create a Crucible CFG from a list of blocks
addBlocksCFG :: forall s arch ids
             .  MacawSymbolicArchFunctions arch
             -- ^ Crucible specific functions.
              -> M.ArchSegmentOff arch
                 -- ^ Address of start of block
             ->  (M.ArchAddrWord arch -> WPL.Position)
             -- ^ Function that maps offsets from start of block to Crucible position.
             -> M.Block arch ids
             -- ^ Macaw block for this region.
             -> MacawMonad arch ids s (CR.Label s, [CR.Block (MacawExt arch) s (MacawFunctionResult arch)])
addBlocksCFG archFns addr posFn macawBlock = do
  crucGenArchConstraints archFns $ do
   -- Map block map to Crucible CFG
  entry <- CR.Label <$> mmFreshNonce
  (blk,blks) <- addMacawBlock archFns addr entry posFn macawBlock
  return (entry, blk:blks)

-- | Create a registerized Crucible CFG from an arbitrary list of macaw blocks
--
-- Note that this variant takes macaw 'M.Block' blocks - these are blocks as
-- returned from the architecture-specific disassembler and are /not/ the parsed
-- blocks returned by the code discovery (i.e., not those found in
-- 'M.DiscoveryFunInfo').
--
-- Also note that any 'M.FetchAndExecute' terminators are turned into Crucible
-- return statements.
mkBlocksRegCFG :: forall arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible specific functions.
            -> C.HandleAllocator
               -- ^ Handle allocator to make the blocks
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> M.ArchSegmentOff arch
               -- ^ Address for start of block.
            -> (M.ArchAddrWord arch -> WPL.Position)
            -- ^ Function that maps offsets from start of block to Crucible position.
            -> M.Block arch ids
            -- ^ List of blocks for this region.
            -> IO (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlocksRegCFG archFns halloc nm addr posFn macawBlock = do
  mkCrucRegCFG archFns halloc nm $ do
    addBlocksCFG archFns addr posFn macawBlock

-- | Create a Crucible CFG from an arbitrary list of macaw blocks
--
-- Note that this variant takes macaw 'M.Block' blocks - these are blocks as
-- returned from the architecture-specific disassembler and are /not/ the parsed
-- blocks returned by the code discovery (i.e., not those found in
-- 'M.DiscoveryFunInfo').
--
-- Also note that any 'M.FetchAndExecute' terminators are turned into Crucible
-- return statements.
mkBlocksCFG :: forall arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible specific functions.
            -> C.HandleAllocator
               -- ^ Handle allocator to make the blocks
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> M.ArchSegmentOff arch
               -- ^ Address for start of block.
            -> (M.ArchAddrWord arch -> WPL.Position)
            -- ^ Function that maps offsets from start of block to Crucible position.
            -> M.Block arch ids
            -- ^ List of blocks for this region.
            -> IO (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlocksCFG archFns halloc nm addr posFn macawBlock =
  toCoreCFG archFns <$>
  mkBlocksRegCFG archFns halloc nm addr posFn macawBlock

-- | Create a map from Macaw @(address, index)@ pairs to Crucible labels
mkBlockLabelMap :: [M.ParsedBlock arch ids] -> MacawMonad arch ids s (BlockLabelMap arch s)
mkBlockLabelMap blks = foldM insBlock Map.empty blks
 where insBlock :: BlockLabelMap arch s -> M.ParsedBlock arch ids -> MacawMonad arch ids s (BlockLabelMap arch s)
       insBlock m b = do
         let base = M.pblockAddr b
         n <- mmFreshNonce
         pure $! Map.insert base (CR.Label n) m

-- | Normalise any term statements to returns --- i.e., remove branching, jumping, etc.
--
-- This is used when translating a single Macaw block into Crucible, as Crucible
-- functions must end in a return.
termStmtToReturn :: forall arch ids. M.ParsedTermStmt arch ids -> M.ParsedTermStmt arch ids
termStmtToReturn tm0 =
  case tm0 of
    M.ParsedReturn{} -> tm0
    M.ParsedCall r _ -> M.ParsedReturn r
    M.ParsedJump r _ -> M.ParsedReturn r
    M.ParsedBranch r _ _ _ -> M.ParsedReturn r
    M.ParsedLookupTable _layout r _ _ -> M.ParsedReturn r
    M.ParsedArchTermStmt _ r _ -> M.ParsedReturn r
    M.ClassifyFailure r _ -> M.ParsedReturn r
    M.PLTStub{} -> tm0
    M.ParsedTranslateError{} -> tm0

-- | Normalise any term statements to jumps.
termStmtToJump
  :: forall arch ids
   . M.ParsedTermStmt arch ids
  -> M.ArchSegmentOff arch
  -> M.ParsedTermStmt arch ids
termStmtToJump tm0 addr =
  case tm0 of
    M.ParsedJump r _ -> M.ParsedJump r addr
    M.ParsedBranch r _ _ _ -> M.ParsedJump r addr
    M.ParsedCall r _ -> M.ParsedJump r addr
    M.ParsedReturn r -> M.ParsedJump r addr
    M.ParsedLookupTable _layout r _ _ -> M.ParsedJump r addr
    M.ParsedArchTermStmt _ r _ -> M.ParsedJump r addr
    M.ClassifyFailure r _ -> M.ParsedJump r addr
    M.PLTStub{} -> tm0
    M.ParsedTranslateError{} -> tm0

-- | Create a registerized Crucible CFG from a single Macaw 'M.ParsedBlock'.
-- Note that the term statement of the block is updated to make it a return (and
-- thus make a valid Crucible CFG).
--
-- Note that this function takes 'M.ParsedBlock's, which are the blocks
-- available in the 'M.DiscoveryFunInfo'.
--
-- This is useful as an alternative to 'mkParsedBlockCFG' if post-processing is
-- desired (as this is easier on the registerized form). Use 'toCoreCFG' to
-- finish by translating the registerized CFG to SSA.
mkParsedBlockRegCFG :: forall arch ids
                 .  MacawSymbolicArchFunctions arch
                 -- ^ Architecture specific functions.
                 -> C.HandleAllocator
                 -- ^ Handle allocator to make the blocks
                 -> (M.ArchSegmentOff arch -> WPL.Position)
                 -- ^ Function that maps function address to Crucible position
                 -> M.ParsedBlock arch ids
                 -- ^ Block to translate
                 -> IO (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkParsedBlockRegCFG archFns halloc posFn b = crucGenArchConstraints archFns $ do
  mkCrucRegCFG archFns halloc "" $ do
    let strippedBlock = b { M.pblockTermStmt = termStmtToReturn (M.pblockTermStmt b) }

    let entryAddr = M.pblockAddr strippedBlock

    -- Get type for representing Machine registers
    let regType = C.StructRepr (crucArchRegTypes archFns)
    let entryPos = posFn entryAddr
    -- Create Crucible "register" (i.e. a mutable variable) for
    -- current value of Macaw machine registers.
    regRegId <- mmFreshNonce
    let regReg = CR.Reg { CR.regPosition = entryPos
                        , CR.regId = regRegId
                        , CR.typeOfReg = regType
                        }
    ng <- mmNonceGenerator
    -- Create atom for entry
    inputAtom <- Ctx.last <$> (mmExecST $ CR.mkInputAtoms ng entryPos (Empty :> regType))
    -- Create map from Macaw (address,blockId pairs) to Crucible labels
    blockLabelMap :: BlockLabelMap arch s <-
      mkBlockLabelMap [strippedBlock]

    -- Get initial block for Crucible
    entryLabel <- CR.Label <$> mmFreshNonce
    let initPosFn :: M.ArchAddrWord arch -> WPL.Position
        initPosFn off = posFn r
          where Just r = M.incSegmentOff entryAddr (toInteger off)
    (initCrucibleBlock,initExtraCrucibleBlocks) <-
      runCrucGen archFns initPosFn entryLabel regReg $ do
        -- Initialize value in regReg with initial registers
        setMachineRegs inputAtom
        -- Jump to function entry point
        addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap entryAddr)

    -- Generate code for Macaw block after entry
    crucibleBlock <- addParsedBlock archFns blockLabelMap [] posFn regReg strippedBlock

    -- (stubCrucibleBlocks,_) <- unzip <$>
    --   (forM (Map.elems stubMap)$ \c -> do
    --      runCrucGen archFns memBaseVarMap initPosFn 0 c regReg $ do
    --        r <- getRegs
    --        addTermStmt (CR.Return r))

    -- Return initialization block followed by actual blocks.
    pure (entryLabel, initCrucibleBlock : initExtraCrucibleBlocks ++ crucibleBlock)

-- | This create a Crucible CFG from a Macaw block.  Note that the
-- term statement of the block is updated to make it a return.
--
-- Note that this function takes 'M.ParsedBlock's, which are the blocks
-- available in the 'M.DiscoveryFunInfo'.
mkParsedBlockCFG :: forall arch ids
                 .  MacawSymbolicArchFunctions arch
                 -- ^ Architecture specific functions.
                 -> C.HandleAllocator
                 -- ^ Handle allocator to make the blocks
                 -> (M.ArchSegmentOff arch -> WPL.Position)
                 -- ^ Function that maps function address to Crucible position
                 -> M.ParsedBlock arch ids
                 -- ^ Block to translate
                 -> IO (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkParsedBlockCFG archFns halloc posFn b =
  toCoreCFG archFns <$> mkParsedBlockRegCFG archFns halloc posFn b

parsedTermTargets :: M.ParsedTermStmt arch ids -> [M.ArchSegmentOff arch]
parsedTermTargets t =
  case t of
    M.ParsedCall _ Nothing -> []
    M.ParsedCall _ (Just ret) -> [ret]
    M.ParsedJump _ addr -> [addr]
    M.ParsedBranch _ _ taddr faddr -> [taddr, faddr]
    M.ParsedLookupTable _layout _ _ addrs -> F.toList addrs
    M.ParsedReturn {} -> []
    M.ParsedArchTermStmt _ _ Nothing -> []
    M.ParsedArchTermStmt _ _ (Just addr) -> [addr]
    M.PLTStub {} -> []
    M.ParsedTranslateError {} -> []
    M.ClassifyFailure {} -> []

-- | See the documentation for 'mkBlockSliceCFG'
mkBlockSliceRegCFG :: forall arch ids
                    . MacawSymbolicArchFunctions arch
                   -> C.HandleAllocator
                   -> (M.ArchSegmentOff arch -> WPL.Position)
                   -> M.ParsedBlock arch ids
                   -- ^ Entry block
                   -> [M.ParsedBlock arch ids]
                   -- ^ Non-entry non-terminal blocks
                   -> [M.ParsedBlock arch ids]
                   -- ^ Terminal blocks
                   -> [(M.ArchSegmentOff arch, M.ArchSegmentOff arch)]
                   -- ^ (Source, target) block address pairs to convert to returns
                   -> Maybe (CR.GlobalVar (MacawBlockEndType arch))
                   -- ^ variable to optionally retain how the block originally exited
                   -> IO (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlockSliceRegCFG archFns halloc posFn entry body0 terms retEdges_ block_end_var = crucGenArchConstraints archFns $ mkCrucRegCFG archFns halloc "" $ do
  -- Build up some initial values needed to set up the entry point to the
  -- function (including the initial value of all registers)
  inputRegId <- mmFreshNonce
  let inputReg = CR.Reg { CR.regPosition = entryPos
                        , CR.regId = inputRegId
                        , CR.typeOfReg = archRegTy
                        }
  ng <- mmNonceGenerator
  inputAtom <- mmExecST (Ctx.last <$> CR.mkInputAtoms ng entryPos (Empty :> archRegTy))

  -- Allocate Crucible CFG labels for all of the blocks provided by the caller
  labelMap0 <- mkBlockLabelMap allBlocks

  -- Add synthetic blocks for all jump targets mentioned by the input blocks,
  -- but not included in the list of all blocks.  The synthetic blocks simply
  -- assume False to indicate to the symbolic execution engine that executions
  -- reaching those missing blocks are not feasible paths.
  (labelMap, syntheticBlocks) <- F.foldlM (makeSyntheticBlocks inputReg) (labelMap0, []) allBlocks

  -- Add synthetic block to act as a target for jumps that we want to be
  -- returns instead.
  (retLabel, retBlocks) <- makeReturnBlock inputReg
  let lookupRetEdges src = Map.fromSet
        (const retLabel)
        (Map.findWithDefault S.empty src retEdges)

  -- Set up a fake entry block that initializes the register file and jumps
  -- to the real entry point
  entryLabel <- CR.Label <$> mmFreshNonce
  (initCrucBlock, initExtraCrucBlocks) <- runCrucGen archFns (offPosFn entryAddr) entryLabel inputReg $ do
    setMachineRegs inputAtom
    addTermStmt $ CR.Jump (parsedBlockLabel labelMap entryAddr)

  -- Add each block in the slice
  --
  -- For blocks marked as terminators, we rewrite their terminator statement
  -- into a return.
  crucBlocks <- forM allBlocks $ \block -> do
    let blockAddr = M.pblockAddr block
    let label = case Map.lookup blockAddr labelMap of
          Just lbl -> lbl
          Nothing -> error ("Missing block label for block at " ++ show blockAddr)

    -- Below, we are going to call addMacawParsedTermStmt to convert the final
    -- instruction in this macaw block into an edge in the CFG. Under normal
    -- circumstances, this happens by keeping a static map from addresses (that
    -- are the targets of jumps) to CFG nodes, and passing that map as ane of
    -- the arguments.
    --
    -- We are going to corrupt that mechanism slightly. We want to allow
    -- callers to break cycles in the CFG by converting some jumps into returns
    -- instead, and the API we've chosen for specifying which jumps is by
    -- identifying source block/target block pairs whose edges we should drop
    -- from the CFG to break the cycles. Right here is where we implement that
    -- breakage. The way we do it is by changing the map from targets to nodes
    -- differently depending on which source block we are currently
    -- interpreting.
    --
    -- So: lookupRetEdges builds an override Map which points some of the
    -- possible target blocks at a special CFG node that just returns
    -- immediately. Then labelMapWithReturns has the usual static map, but with
    -- those targets overridden appropriately.
    let labelMapWithReturns = Map.union (lookupRetEdges blockAddr) labelMap
    (mainCrucBlock, auxCrucBlocks) <- runCrucGen archFns (offPosFn blockAddr) label inputReg $ do
      mapM_ (addMacawStmt blockAddr) (M.pblockStmts block)
      assignBlockEnd archFns block_end_var (termStmtToBlockEnd $ M.pblockTermStmt block)
      case S.member blockAddr termAddrs of
        True -> do
          -- NOTE: If the entry block is also a terminator, we'll just
          -- return at the end of the entry block and ignore all other
          -- blocks.  This is the intended behavior, but it is an
          -- interesting consequence.

          -- Convert the existing terminator into a return.  This function
          -- preserves the existing register state, which is important when
          -- generating the Crucible return.
          let retTerm = termStmtToReturn (M.pblockTermStmt block)
          addMacawParsedTermStmt labelMapWithReturns [] blockAddr retTerm
        False -> addMacawParsedTermStmt labelMapWithReturns [] blockAddr (M.pblockTermStmt block)
    return (reverse (mainCrucBlock : auxCrucBlocks))
  return (entryLabel, initCrucBlock : (initExtraCrucBlocks ++ concat crucBlocks ++ concat syntheticBlocks ++ retBlocks))
  where
    entryAddr = M.pblockAddr entry
    entryPos = posFn entryAddr
    archRegTy = C.StructRepr (crucArchRegTypes archFns)
    -- Addresses of blocks marked as terminators
    termAddrs = S.fromList (fmap M.pblockAddr terms)
    retEdges = Map.fromListWith S.union [(src, S.singleton tgt) | (src, tgt) <- retEdges_]

    -- Blocks are "body blocks" if they are not the entry or marked as
    -- terminator blocks.  We need this distinction because we modify terminator
    -- blocks to end in a return (even if they don't naturally do so).
    isBodyBlock :: M.ParsedBlock arch ids -> Bool
    isBodyBlock pb = not (S.member (M.pblockAddr pb) termAddrs) && M.pblockAddr pb /= entryAddr

    -- Blocks that are not the entry or terminators
    realBody = filter isBodyBlock body0
    -- The list of all blocks without duplicates
    allBlocks = entry : (realBody ++ terms)

    offPosFn :: (M.MemWidth (M.ArchAddrWidth arch)) => M.ArchSegmentOff arch -> M.ArchAddrWord arch -> WPL.Position
    offPosFn base = posFn . fromJust . M.incSegmentOff base . toInteger

    -- There may be blocks that are jumped to but not included in the list of
    -- blocks provided in this slice.  We need to add synthetic blocks to stand in
    -- for them.  The blocks are simple: they just assert False to indicate that
    -- those branches are never taken.
    makeSyntheticBlock :: forall s
                        . (M.MemWidth (M.ArchAddrWidth arch))
                       => CR.Reg s (ArchRegStruct arch)
                       -> (Map.Map (M.ArchSegmentOff arch) (CR.Label s), [[CR.Block (MacawExt arch) s (ArchRegStruct arch)]])
                       -> M.ArchSegmentOff arch
                       -> MacawMonad arch ids s (Map.Map (M.ArchSegmentOff arch) (CR.Label s), [[CR.Block (MacawExt arch) s (ArchRegStruct arch)]])
    makeSyntheticBlock inputReg (lm, blks) baddr =
      case Map.lookup baddr lm of
        Just _ -> return (lm, blks)
        Nothing -> do
          synLabel <- CR.Label <$> mmFreshNonce
          (synBlock, extraSynBlocks) <- runCrucGen archFns (offPosFn baddr) synLabel inputReg $ do
            falseAtom <- valueToCrucible (M.BoolValue False)
            msg <- appAtom (C.StringLit (C.UnicodeLiteral "Elided block"))
            addStmt (CR.Assume falseAtom msg)
            errMsg <- crucibleValue (C.StringLit (C.UnicodeLiteral "Elided block"))
            addTermStmt (CR.ErrorStmt errMsg)
          return (Map.insert baddr synLabel lm, reverse (synBlock : extraSynBlocks) : blks)

    makeSyntheticBlocks :: forall s
                         . (M.MemWidth (M.ArchAddrWidth arch))
                        => CR.Reg s (ArchRegStruct arch)
                        -> (Map.Map (M.ArchSegmentOff arch) (CR.Label s), [[CR.Block (MacawExt arch) s (ArchRegStruct arch)]])
                        -> M.ParsedBlock arch ids
                        -> MacawMonad arch ids s (Map.Map (M.ArchSegmentOff arch) (CR.Label s), [[CR.Block (MacawExt arch) s (ArchRegStruct arch)]])
    makeSyntheticBlocks inputReg (lm, blks) blk =
      F.foldlM (makeSyntheticBlock inputReg) (lm, blks) (parsedTermTargets (M.pblockTermStmt blk))

    makeReturnBlock :: forall s
                     . (M.MemWidth (M.ArchAddrWidth arch))
                    => CR.Reg s (ArchRegStruct arch)
                    -> MacawMonad arch ids s (CR.Label s, [CR.Block (MacawExt arch) s (ArchRegStruct arch)])
    makeReturnBlock inputReg = do
      lbl <- CR.Label <$> mmFreshNonce
      (blk, blks) <- runCrucGen archFns syntheticPos lbl inputReg $ do
        regs <- getRegs
        addTermStmt (CR.Return regs)
      return (lbl, blk:blks)
      where
      syntheticPos w = WPL.OtherPos ("synthetic return block for mkBlockSliceRegCFG; offset " <> T.pack (show w))

-- | Construct a Crucible CFG from a (possibly incomplete) collection of macaw blocks
--
-- The CFG starts with the provided entry block and returns from the terminal
-- block.  Control flow between the remaining (body) blocks is preserved.  If a
-- block ends in a branch to a block not included in the body, the translation
-- will generate a new block that simply asserts false (i.e., that execution
-- should never reach that block).  The terminal block will have its term
-- statement translated into a return.
--
-- The entry and terminal block can be the same, in which case the body is
-- expected to be empty (and will be ignored).
--
-- The intended use of this function is to ask for models of registers after a
-- subset of code in a function has executed by examining the register state
-- after the fragment executes.
mkBlockSliceCFG :: forall arch ids
                 . MacawSymbolicArchFunctions arch
                -> C.HandleAllocator
                -> (M.ArchSegmentOff arch -> WPL.Position)
                -> M.ParsedBlock arch ids
                -- ^ Entry block
                -> [M.ParsedBlock arch ids]
                -- ^ Non-entry non-terminal blocks
                -> [M.ParsedBlock arch ids]
                -- ^ Terminal blocks
                -> [(M.ArchSegmentOff arch, M.ArchSegmentOff arch)]
                -- ^ (Source, target) block address pairs to convert to returns
                -> Maybe (CR.GlobalVar (MacawBlockEndType arch))
                -- ^ variable to optionally retain how the block originally exited
                -> IO (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlockSliceCFG archFns halloc posFn entry body terms retEdges block_end_var =
  toCoreCFG archFns <$> mkBlockSliceRegCFG archFns halloc posFn entry body terms retEdges block_end_var

mkBlockPathRegCFG
  :: forall arch ids
   . MacawSymbolicArchFunctions arch
  -- ^ Architecture specific functions.
  -> C.HandleAllocator
  -- ^ Handle allocator to make the blocks
  -> (M.ArchSegmentOff arch -> WPL.Position)
  -- ^ Function that maps function address to Crucible position
  -> [M.ParsedBlock arch ids]
  -- ^ Bloc path to translate
  -> IO (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlockPathRegCFG arch_fns halloc pos_fn blocks =
  crucGenArchConstraints arch_fns $ mkCrucRegCFG arch_fns halloc "" $ do
    let entry_addr = M.pblockAddr $ head blocks
    let first_blocks = zipWith
          (\block next_block ->
            block { M.pblockTermStmt = termStmtToJump (M.pblockTermStmt block) (M.pblockAddr next_block) })
          (take (length blocks - 1) blocks)
          (tail blocks)
    let last_block = (last blocks) { M.pblockTermStmt = termStmtToReturn (M.pblockTermStmt (last blocks)) }
    let block_path = first_blocks ++ [last_block]

    -- Get type for representing Machine registers
    let arch_reg_struct_type = C.StructRepr $ crucArchRegTypes arch_fns
    let entry_pos = pos_fn entry_addr
    -- Create Crucible "register" (i.e. a mutable variable) for
    -- current value of Macaw machine registers.
    arch_reg_struct_reg_id <- mmFreshNonce
    let arch_reg_struct_reg = CR.Reg
          { CR.regPosition = entry_pos
          , CR.regId = arch_reg_struct_reg_id
          , CR.typeOfReg = arch_reg_struct_type
          }
    nonce_gen <- mmNonceGenerator
    -- Create atom for entry
    input_atom <- mmExecST $ Ctx.last <$>
      CR.mkInputAtoms nonce_gen entry_pos (Empty :> arch_reg_struct_type)

    -- Create map from Macaw (block_address, statement_list_id) pairs
    -- to Crucible labels
    block_label_map :: BlockLabelMap arch s <- mkBlockLabelMap block_path

    let off_pos_fn :: M.ArchSegmentOff arch -> M.ArchAddrWord arch -> WPL.Position
        off_pos_fn base = pos_fn . fromJust . M.incSegmentOff base . toInteger

    let runCrucGen' addr label = runCrucGen
          arch_fns
          (off_pos_fn addr)
          label
          arch_reg_struct_reg

    -- Generate entry Crucible block
    entry_label <- CR.Label <$> mmFreshNonce
    (init_crucible_block, init_extra_crucible_blocks) <-
      runCrucGen' entry_addr entry_label $ do
        -- Initialize value in arch_reg_struct_reg with initial registers
        setMachineRegs input_atom
        -- Jump to function entry point
        addTermStmt $ CR.Jump (parsedBlockLabel block_label_map entry_addr)

    -- Generate code for Macaw blocks
    crucible_blocks <- forM block_path $ \block -> do
      let block_addr = M.pblockAddr block
      let label = block_label_map Map.! block_addr

      (first_crucible_block, first_extra_crucible_blocks) <- runCrucGen' block_addr label $ do
        arch_width <- archAddrWidth
        ip_reg_val <- getRegValue M.ip_reg
        block_ptr <- evalMacawStmt $
          MacawGlobalPtr arch_width $ M.segoffAddr block_addr
        cond <- evalMacawStmt $ PtrEq arch_width ip_reg_val block_ptr
        msg <- appAtom $ C.StringLit $ C.UnicodeLiteral
          "the current block follows the previous block in the path"
        addStmt $ CR.Assume cond msg

        mapM_ (addMacawStmt block_addr) (M.pblockStmts block)
        addMacawParsedTermStmt block_label_map [] block_addr (M.pblockTermStmt block)
      pure (reverse (first_crucible_block:first_extra_crucible_blocks))

    pure (entry_label, init_crucible_block :
                         init_extra_crucible_blocks ++ concat crucible_blocks)

mkBlockPathCFG
  :: forall arch ids
   . MacawSymbolicArchFunctions arch
  -- ^ Architecture specific functions.
  -> C.HandleAllocator
  -- ^ Handle allocator to make the blocks
  -> (M.ArchSegmentOff arch -> WPL.Position)
  -- ^ Function that maps function address to Crucible position
  -> [M.ParsedBlock arch ids]
  -- ^ Block to translate
  -> IO (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlockPathCFG arch_fns halloc pos_fn blocks =
  toCoreCFG arch_fns <$>
    mkBlockPathRegCFG arch_fns halloc pos_fn blocks

-- | Translate a macaw function (passed as a 'M.DiscoveryFunInfo') into a
-- registerized Crucible CFG
--
-- This is provided as an alternative to 'mkFunCFG' to allow for post-processing
-- of the CFG (e.g., instrumentation) prior to the SSA conversion (which can be
-- done using 'toCoreCFG').
mkFunRegCFG :: forall arch ids
         .  MacawSymbolicArchFunctions arch
            -- ^ Architecture specific functions.
         -> C.HandleAllocator
            -- ^ Handle allocator to make the blocks
         -> C.FunctionName
            -- ^ Name of function for pretty print purposes.
         -> (M.ArchSegmentOff arch -> WPL.Position)
            -- ^ Function that maps function address to Crucible position
         -> M.DiscoveryFunInfo arch ids
         -- ^ List of blocks for this region.
         -> IO (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkFunRegCFG archFns halloc nm posFn fn = crucGenArchConstraints archFns $ do
  mkCrucRegCFG archFns halloc nm $ do
    -- Get entry point address for function
    let entryAddr = M.discoveredFunAddr fn
    -- Get list of blocks
    let blockList = Map.elems (fn^.M.parsedBlocks)
    -- Get type for representing Machine registers
    let regType = C.StructRepr (crucArchRegTypes archFns)
    let entryPos = posFn entryAddr
    -- Create Crucible "register" (i.e. a mutable variable) for
    -- current value of Macaw machine registers.
    regRegId <- mmFreshNonce
    let regReg = CR.Reg { CR.regPosition = entryPos
                        , CR.regId = regRegId
                        , CR.typeOfReg = regType
                        }
    -- Create atom for entry
    ng <- mmNonceGenerator
    inputAtom <- Ctx.last <$> (mmExecST $ CR.mkInputAtoms ng entryPos (Empty :> regType))
    -- Create map from Macaw (address,blockId pairs) to Crucible labels
    blockLabelMap :: BlockLabelMap arch s <-
      mkBlockLabelMap blockList
    -- Get initial block for Crucible
    entryLabel <- CR.Label <$> mmFreshNonce
    let initPosFn :: M.ArchAddrWord arch -> WPL.Position
        initPosFn off = posFn r
          where Just r = M.incSegmentOff entryAddr (toInteger off)
    (initCrucibleBlock,initExtraCrucibleBlocks) <-
      runCrucGen archFns initPosFn entryLabel regReg $ do
        -- Initialize value in regReg with initial registers
        setMachineRegs inputAtom
        -- Jump to function entry point
        addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap entryAddr)

    -- Generate code for Macaw blocks after entry
    restCrucibleBlocks <-
      forM blockList $ \b -> do
        addParsedBlock archFns blockLabelMap (M.discoveredClassifyFailureResolutions fn) posFn regReg b
    -- Return initialization block followed by actual blocks.
    pure (entryLabel, initCrucibleBlock :
                        initExtraCrucibleBlocks ++ concat restCrucibleBlocks)

-- | Translate a macaw function (passed as a 'M.DiscoveryFunInfo') into a Crucible 'C.CFG' (in SSA form)
mkFunCFG :: forall arch ids
         .  MacawSymbolicArchFunctions arch
            -- ^ Architecture specific functions.
         -> C.HandleAllocator
            -- ^ Handle allocator to make the blocks
         -> C.FunctionName
            -- ^ Name of function for pretty print purposes.
         -> (M.ArchSegmentOff arch -> WPL.Position)
            -- ^ Function that maps function address to Crucible position
         -> M.DiscoveryFunInfo arch ids
            -- ^ List of blocks for this region.
         -> IO (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkFunCFG archFns halloc nm posFn fn =
  toCoreCFG archFns <$> mkFunRegCFG archFns halloc nm posFn fn

-- | Generate the final SSA CFG from a registerized CFG. Offered
-- separately in case post-processing on the registerized CFG is
-- desired.
toCoreCFG :: MacawSymbolicArchFunctions arch
          -> CR.SomeCFG (MacawExt arch) init ret
          -- ^ A registerized Crucible CFG
          -> C.SomeCFG (MacawExt arch) init ret
toCoreCFG archFns (CR.SomeCFG cfg) = crucGenArchConstraints archFns $ C.toSSA cfg

-- * Retaining original macaw block endings when slicing CFG

-- | An enum corresponding to the kind of terminal statement that originally
-- appeared at the end of a block.
data MacawBlockEndCase =
    MacawBlockEndJump
  | MacawBlockEndCall
  | MacawBlockEndReturn
  | MacawBlockEndBranch
  | MacawBlockEndArch
  | MacawBlockEndFail
  deriving (Eq, Ord, Enum, Bounded)

-- | A summary of a 'M.ParsedTermStmt', representing how the block ended and
-- potentally the address to return to in the case of a function call.
data MacawBlockEnd arch = MacawBlockEnd MacawBlockEndCase !(Maybe (M.ArchSegmentOff arch))

-- | A crucible encoding of 'MacawBlockEnd', where the 'MacawBlockEndCase' as a 3-bit bitvector
-- and the return address is a 'MM.LLVMPointerType'.
type MacawBlockEndType arch = C.StructType (Ctx.EmptyCtx Ctx.::> C.BVType 3 Ctx.::> C.MaybeType (MM.LLVMPointerType (M.ArchAddrWidth arch)))

blockEndAtom :: forall arch ids s
              . MacawSymbolicArchFunctions arch 
             -> MacawBlockEnd arch
             -> CrucGen arch ids s (CR.Atom s (MacawBlockEndType arch))
blockEndAtom archFns (MacawBlockEnd blendK mret) = crucGenArchConstraints archFns $ do
    blendK' <- CG.bvLit knownNat (toInteger $ fromEnum blendK)
    let
      memWidthNatRepr = M.memWidthNatRepr @(M.ArchAddrWidth arch)
      ptrRepr = MM.LLVMPointerRepr memWidthNatRepr
    mret' <- case mret of
      Just addr -> do
        ptr <- valueToCrucible $ M.RelocatableValue (M.addrWidthRepr (Proxy @(M.ArchAddrWidth arch))) (M.segoffAddr addr)
        appAtom $ C.JustValue ptrRepr ptr
      Nothing -> do
        appAtom $ C.NothingValue ptrRepr
    let repr = Ctx.empty Ctx.:> C.BVRepr knownNat Ctx.:> C.MaybeRepr ptrRepr
    appAtom $ C.MkStruct repr (Ctx.empty Ctx.:> blendK' Ctx.:> mret')

assignBlockEnd :: MacawSymbolicArchFunctions arch
               -> Maybe (CR.GlobalVar (MacawBlockEndType arch))
               -> MacawBlockEnd arch
               -> CrucGen arch ids s ()
assignBlockEnd _ Nothing _ = return ()
assignBlockEnd archFns (Just blendVar) blend = do
  blend' <- blockEndAtom archFns blend
  addStmt $ CR.WriteGlobal blendVar blend'

isBlockEndCase :: IsSymInterface sym
               => Proxy arch
               -> sym
               -> C.RegValue sym (MacawBlockEndType arch)
               -> MacawBlockEndCase
               -> IO (Pred sym)
isBlockEndCase _ sym (_ Ctx.:> C.RV blendC' Ctx.:> _) blendC = do
  blendC'' <- bvLit sym knownNat (BV.mkBV knownNat (toInteger $ fromEnum blendC))
  isEq sym blendC' blendC''

blockEndCase :: IsSymInterface sym
             => Proxy arch
             -> sym
             -> C.RegValue sym (MacawBlockEndType arch)
             -> IO (C.MuxTree sym MacawBlockEndCase)
blockEndCase arch sym blend = do
  foldM addCase (C.toMuxTree sym MacawBlockEndFail) [minBound..maxBound]
  where
    addCase mt blendC = do
      p <- isBlockEndCase arch sym blend blendC
      C.mergeMuxTree sym p (C.toMuxTree sym blendC) mt

blockEndReturn :: Proxy arch
               -> C.RegValue sym (MacawBlockEndType arch)
               -> (C.RegValue sym (C.MaybeType (MM.LLVMPointerType (M.ArchAddrWidth arch))))
blockEndReturn _ (_ Ctx.:> _ Ctx.:> C.RV mret) = mret

initBlockEnd :: IsSymInterface sym
             => Proxy arch
             -> sym
             -> IO (C.RegValue sym (MacawBlockEndType arch))
initBlockEnd _ sym = do
  blendK <- bvLit sym (knownNat @3) (BV.mkBV (knownNat @3) (toInteger $ fromEnum MacawBlockEndReturn))
  return $ (Ctx.empty Ctx.:> C.RV blendK Ctx.:> C.RV Unassigned)

termStmtToBlockEnd :: forall arch ids. M.ParsedTermStmt arch ids -> MacawBlockEnd arch
termStmtToBlockEnd tm0 =
  case tm0 of
    M.ParsedReturn {} -> MacawBlockEnd MacawBlockEndReturn Nothing
    M.ParsedCall _ ret -> MacawBlockEnd MacawBlockEndCall ret
    M.ParsedJump {} -> MacawBlockEnd MacawBlockEndJump Nothing
    M.ParsedBranch {} -> MacawBlockEnd MacawBlockEndBranch Nothing
    M.ParsedLookupTable {} -> MacawBlockEnd MacawBlockEndJump Nothing
    M.ParsedArchTermStmt _ _ ret -> MacawBlockEnd MacawBlockEndArch ret
    M.ClassifyFailure {} -> MacawBlockEnd MacawBlockEndFail Nothing
    M.PLTStub {} -> MacawBlockEnd MacawBlockEndCall Nothing
    M.ParsedTranslateError{} -> MacawBlockEnd MacawBlockEndFail Nothing

-- * Symbolic simulation

evalMacawExprExtension :: forall sym arch f tp
                       .  IsSymInterface sym
                       => sym
                       -> C.IntrinsicTypes sym
                       -> (Int -> String -> IO ())
                       -> (forall utp . f utp -> IO (C.RegValue sym utp))
                       -> MacawExprExtension arch f tp
                       -> IO (C.RegValue sym tp)
evalMacawExprExtension sym _iTypes _logFn f e0 =
  case e0 of

    MacawOverflows op w xv yv cv -> do
      x <- f xv
      y <- f yv
      c <- f cv
      let w' = incNat w
      Just LeqProof <- pure $ testLeq (knownNat :: NatRepr 1) w'
      one  <- What4.Interface.bvLit sym w' (BV.one w')
      zero <- What4.Interface.bvLit sym w' (BV.zero w')
      cext <- baseTypeIte sym c one zero
      case op of
        Uadc -> do
          -- Unsigned add overflow occurs if largest bit is set.
          xext <- bvZext sym w' x
          yext <- bvZext sym w' y
          zext <- join $ bvAdd sym <$> bvAdd sym xext yext <*> pure cext
          bvIsNeg sym zext
        Sadc -> do
          xext <- bvSext sym w' x
          yext <- bvSext sym w' y
          zext <- join $ bvAdd sym <$> bvAdd sym xext yext <*> pure cext
          znorm <- bvSext sym w' =<< bvTrunc sym w zext
          bvNe sym zext znorm
        Usbb -> do
          xext <- bvZext sym w' x
          yext <- bvZext sym w' y
          zext <- join $ bvSub sym <$> bvSub sym xext yext <*> pure cext
          bvIsNeg sym zext
        Ssbb -> do
          xext <- bvSext sym w' x
          yext <- bvSext sym w' y
          zext <- join $ bvSub sym <$> bvSub sym xext yext <*> pure cext
          znorm <- bvSext sym w' =<< bvTrunc sym w zext
          bvNe sym zext znorm

    PtrToBits _w x  -> doPtrToBits sym =<< f x
    BitsToPtr _w x  -> MM.llvmPointer_bv sym =<< f x

    MacawNullPtr w | LeqProof <- addrWidthIsPos w -> MM.mkNullPointer sym (M.addrWidthNatRepr w)
    MacawBitcast xExpr eqPr -> do
      x <- f xExpr
      doBitcast sym x eqPr

-- | A use of a pointer in a memory operation
--
-- Uses can be reads or writes (see 'PointerUseTag').  The location is used to
-- produce diagnostics where possible.
data PointerUse = PointerUse (Maybe WPL.ProgramLoc) PointerUseTag

-- | Tag a use of a pointer ('PointerUse') as a read or a write
data PointerUseTag = PointerRead | PointerWrite
  deriving (Eq, Show)

-- | Extract a location from a 'PointerUse', defaulting to the initial location
-- if none was provided
pointerUseLocation :: PointerUse -> WPL.ProgramLoc
pointerUseLocation (PointerUse mloc _) =
  case mloc of
    Just loc -> loc
    Nothing -> WPL.initializationLoc

-- | Extract the tag denoting a 'PointerUse' as a read or a write
pointerUseTag :: PointerUse -> PointerUseTag
pointerUseTag (PointerUse _ tag) = tag

-- | A function to construct validity predicates for pointer uses
--
-- This function creates an assertion that encodes the validity of a global
-- pointer.  One of the intended use cases is that this can be used to generate
-- assertions that memory accesses are limited to some mapped range of memory.
-- It could also be used to prohibit reads from or writes to distinguished
-- regions of the address space.
--
-- Note that macaw-symbolic is agnostic to the semantics of the produced
-- assertion.  A verification tool could simply use @return Nothing@ as the
-- implementation to elide extra memory safety checks, or if they are not
-- required for the desired memory model.
type MkGlobalPointerValidityAssertion sym w = sym
                                            -- ^ The symbolic backend in use
                                            -> PointerUse
                                            -- ^ A tag marking the pointer use as a read or a write
                                            -> Maybe (C.RegEntry sym C.BoolType)
                                            -- ^ If this is a conditional read or write, the predicate
                                            -- determining whether or not the memory operation is executed.  If
                                            -- generating safety assertions, they should account for the presence and
                                            -- value of this predicate.
                                            -> C.RegEntry sym (MM.LLVMPointerType w)
                                            -- ^ The address written to or read from
                                            -> IO (Maybe (Assertion sym))

-- | This evaluates a Macaw statement extension in the simulator.
execMacawStmtExtension
  :: forall sym arch
  . (IsSymInterface sym, MM.HasLLVMAnn sym)
  => SB.MacawArchEvalFn sym MM.Mem arch
  -- ^ Simulation-time interpretations of architecture-specific functions
  -> C.GlobalVar MM.Mem
  -- ^ The distinguished global variable holding the current state of the memory model
  -> MO.GlobalMap sym MM.Mem (M.ArchAddrWidth arch)
  -- ^ The translation from machine words to LLVM memory model pointers
  -> MO.LookupFunctionHandle sym arch
  -- ^ A function to turn machine addresses into Crucible function
  -- handles (which can also perform lazy CFG creation)
  -> MO.LookupSyscallHandle sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> MkGlobalPointerValidityAssertion sym (M.ArchAddrWidth arch)
  -- ^ A function to make memory validity predicates (see 'MkGlobalPointerValidityAssertion' for details)
  -> SB.MacawEvalStmtFunc (MacawStmtExtension arch) (MacawSimulatorState sym) sym (MacawExt arch)
execMacawStmtExtension (SB.MacawArchEvalFn archStmtFn) mvar globs (MO.LookupFunctionHandle lookupH) (MO.LookupSyscallHandle lookupSyscall) toMemPred s0 st =
  case s0 of
    MacawReadMem addrWidth memRep ptr0 -> do
      let sym = st^.C.stateSymInterface
      mem <- getMem st mvar
      ptr <- tryGlobPtr sym mem globs (C.regValue ptr0)
      let puse = PointerUse (st ^. C.stateLocation) PointerRead
      mGlobalPtrValid <- toMemPred sym puse Nothing ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> addAssertion sym globalPtrValid
        Nothing -> return ()
      (,st) <$> doReadMem sym mem addrWidth memRep ptr
    MacawCondReadMem addrWidth memRep cond ptr0 condFalseValue -> do
      let sym = st^.C.stateSymInterface
      mem <- getMem st mvar
      ptr <- tryGlobPtr sym mem globs (C.regValue ptr0)
      let puse = PointerUse (st ^. C.stateLocation) PointerRead
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> addAssertion sym globalPtrValid
        Nothing -> return ()
      (,st) <$> doCondReadMem sym mem addrWidth memRep (C.regValue cond) ptr (C.regValue condFalseValue)
    MacawWriteMem addrWidth memRep ptr0 v -> do
      let sym = st^.C.stateSymInterface
      mem <- getMem st mvar
      ptr <- tryGlobPtr sym mem globs (C.regValue ptr0)
      let puse = PointerUse (st ^. C.stateLocation) PointerWrite
      mGlobalPtrValid <- toMemPred sym puse Nothing ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> addAssertion sym globalPtrValid
        Nothing -> return ()
      mem1 <- doWriteMem sym mem addrWidth memRep ptr (C.regValue v)
      pure ((), setMem st mvar mem1)
    MacawCondWriteMem addrWidth memRep cond ptr0 v -> do
      let sym = st^.C.stateSymInterface
      mem <- getMem st mvar
      ptr <- tryGlobPtr sym mem globs (C.regValue ptr0)
      let puse = PointerUse (st ^. C.stateLocation) PointerWrite
      mGlobalPtrValid <- toMemPred sym puse (Just cond) ptr0
      case mGlobalPtrValid of
        Just globalPtrValid -> addAssertion sym globalPtrValid
        Nothing -> return ()
      mem1 <- doCondWriteMem sym mem addrWidth memRep (C.regValue cond) ptr (C.regValue v)
      pure ((), setMem st mvar mem1)
    MacawGlobalPtr w addr ->
      M.addrWidthClass w $ doGetGlobal st mvar globs addr

    MacawFreshSymbolic t -> -- XXX: user freshValue
      do nm <- case userSymbol "macawFresh" of
                 Right a -> return a
                 Left err -> fail (show err)
         v <- case t of
               M.BoolTypeRepr -> freshConstant sym nm C.BaseBoolRepr
               _ -> error ("MacawFreshSymbolic: XXX type " ++ show t)
         return (v,st)
      where sym = st^.C.stateSymInterface

    MacawLookupFunctionHandle _ args -> do
      (hv, st') <- doLookupFunctionHandle lookupH st mvar (C.regValue args)
      return (C.HandleFnVal hv, st')

    MacawLookupSyscallHandle argReprs retRepr argStruct -> do
      -- Note that unlike 'MacawLookupFunctionHandle', the system call lookup
      -- function does not require access to memory
      (hv, st') <- lookupSyscall argReprs retRepr st argStruct
      return (C.HandleFnVal hv, st')

    MacawArchStmtExtension s    -> archStmtFn mvar globs s st
    MacawArchStateUpdate {}     -> return ((), st)
    MacawInstructionStart {}    -> return ((), st)

    PtrEq  w x y                -> doPtrEq st mvar w x y
    PtrLt  w x y                -> doPtrLt st mvar w x y
    PtrLeq w x y                -> doPtrLeq st mvar w x y
    PtrMux w c x y              -> doPtrMux (C.regValue c) st mvar w x y
    PtrAdd w x y                -> doPtrAdd st mvar w x y
    PtrSub w x y                -> doPtrSub st mvar w x y
    PtrAnd w x y                -> doPtrAnd st mvar w x y
    PtrXor w x y                -> doPtrXor st mvar w x y


-- | Return macaw extension evaluation functions.
macawExtensions
  :: (IsSymInterface sym, MM.HasLLVMAnn sym)
  => SB.MacawArchEvalFn sym MM.Mem arch
  -- ^ A set of interpretations for architecture-specific functions
  -> C.GlobalVar MM.Mem
  -- ^ The Crucible global variable containing the current state of the memory
  -- model
  -> GlobalMap sym MM.Mem (M.ArchAddrWidth arch)
  -- ^ A function that maps bitvectors to valid memory model pointers
  -> LookupFunctionHandle sym arch
  -- ^ A function to translate virtual addresses into function handles
  -- dynamically during symbolic execution
  -> MO.LookupSyscallHandle sym arch
  -- ^ A function to examine the machine state to determine which system call
  -- should be invoked; returns the function handle to invoke
  -> MkGlobalPointerValidityAssertion sym (M.ArchAddrWidth arch)
  -- ^ A function to make memory validity predicates (see 'MkGlobalPointerValidityAssertion' for details)
  -> C.ExtensionImpl (MacawSimulatorState sym) sym (MacawExt arch)
macawExtensions f mvar globs lookupH lookupSyscall toMemPred =
  C.ExtensionImpl { C.extensionEval = evalMacawExprExtension
                  , C.extensionExec = execMacawStmtExtension f mvar globs lookupH lookupSyscall toMemPred
                  }

-- | Run the simulator over a contiguous set of code.
runCodeBlock
  :: forall sym arch blocks
   . (C.IsSyntaxExtension (MacawExt arch), IsSymInterface sym, MM.HasLLVMAnn sym)
  => sym
  -> MacawSymbolicArchFunctions arch
  -- ^ Translation functions
  -> SB.MacawArchEvalFn sym MM.Mem arch
  -> C.HandleAllocator
  -> (MM.MemImpl sym, GlobalMap sym MM.Mem (M.ArchAddrWidth arch))
  -> LookupFunctionHandle sym arch
  -> MO.LookupSyscallHandle sym arch
  -> MkGlobalPointerValidityAssertion sym (M.ArchAddrWidth arch)
  -> C.CFG (MacawExt arch) blocks (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
  -> Ctx.Assignment (C.RegValue' sym) (MacawCrucibleRegTypes arch)
  -- ^ Register assignment
  -> IO ( C.GlobalVar MM.Mem
        , C.ExecResult
          (MacawSimulatorState sym)
          sym
          (MacawExt arch)
          (C.RegEntry sym (ArchRegStruct arch)))
runCodeBlock sym archFns archEval halloc (initMem,globs) lookupH lookupSyscall toMemPred g regStruct = do
  mvar <- MM.mkMemVar "macaw:codeblock_llvm_memory" halloc
  let crucRegTypes = crucArchRegTypes archFns
  let macawStructRepr = C.StructRepr crucRegTypes

  let ctx :: C.SimContext (MacawSimulatorState sym) sym (MacawExt arch)
      ctx = let fnBindings = C.insertHandleMap (C.cfgHandle g)
                             (C.UseCFG g (C.postdomInfo g)) $
                             C.emptyHandleMap
                extImpl = macawExtensions archEval mvar globs lookupH lookupSyscall toMemPred
            in C.initSimContext sym llvmIntrinsicTypes halloc stdout
               (C.FnBindings fnBindings) extImpl MacawSimulatorState
  -- Create the symbolic simulator state
  let initGlobals = C.insertGlobal mvar initMem C.emptyGlobals
  let retType = macawStructRepr
  let s = C.InitialState ctx initGlobals C.defaultAbortHandler retType $
            C.runOverrideSim macawStructRepr $ do
                let args :: C.RegMap sym (MacawFunctionArgs arch)
                    args = C.RegMap (Ctx.singleton (C.RegEntry macawStructRepr regStruct))
                crucGenArchConstraints archFns $
                  C.regValue <$> C.callCFG g args
  a <- C.executeCrucible [] s
  return (mvar,a)

-- $translationNaming
--
-- The functions for translating Macaw IR into Crucible are generally provided
-- in two forms: translation into the /registerized/ Crucible CFG
-- (@mkFooRegCFG@) and translation into the SSA Crucible CFG (@mkFooCFG@).  The
-- registerized form can be converted into SSA form with the 'toCoreCFG'
-- function; the registerized variants are provided to make rewriting easier
-- (e.g., through the API provided by Lang.Crucible.Utils.RegRewrite).
--
-- Additionally, translations are available for entire functions, arbitrary
-- collections of basic blocks, and single basic blocks.

-- $translationExample
--
-- Below is a representative example of converting a Macaw function into a Crucible CFG:
--
-- >>> :set -XFlexibleContexts
-- >>> :set -XScopedTypeVariables
-- >>> :set -XTypeApplications
-- >>> :set -XTypeOperators
-- >>> import qualified Data.Macaw.CFG as MC
-- >>> import qualified Data.Macaw.Discovery as MD
-- >>> import qualified Data.Macaw.Symbolic as MS
-- >>> import           Data.Proxy ( Proxy(..) )
-- >>> import qualified Data.Text.Encoding as TE
-- >>> import qualified Data.Text.Encoding.Error as TEE
-- >>> import qualified Lang.Crucible.FunctionHandle as CFH
-- >>> import qualified What4.FunctionName as WFN
-- >>> import qualified What4.ProgramLoc as WPL
-- >>> :{
-- translate :: forall arch ids a
--            . (MS.ArchInfo arch, MC.MemWidth (MC.ArchAddrWidth arch))
--           => MD.DiscoveryFunInfo arch ids
--           -> (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch) -> IO a)
--           -> IO a
-- translate dfi useCFG =
--   case MS.archVals (Proxy @arch) of
--     Nothing -> fail "Architecture does not support symbolic reasoning"
--     Just avals -> do
--       let archFns = MS.archFunctions avals
--       hdlAlloc <- CFH.newHandleAllocator
--       let nameText = TE.decodeUtf8With TEE.lenientDecode (MD.discoveredFunName dfi)
--       let name = WFN.functionNameFromText nameText
--       let posFn addr = WPL.BinaryPos nameText (maybe 0 fromIntegral (MC.segoffAsAbsoluteAddr addr))
--       cfg <- MS.mkFunCFG archFns hdlAlloc name posFn dfi
--       useCFG cfg
-- :}

-- $translationHelpers
--
-- A value of type 'MacawSymbolicArchFunctions' is required to call the
-- translation functions.  Those values are provided by the
-- architecture-specific backends (e.g., macaw-x86-symbolic).  To obtain a value
-- of this type in a more architecture-independent way, see the 'ArchInfo'
-- class, which returns all of the required bits to run macaw-symbolic for a
-- given target architecture.

-- $simulationNotes
--
-- These are all of the helpers required to set up the symbolic simulator to
-- actually run a Crucible CFG constructed from a Macaw program.

-- $simulationExample
--
-- Building on the translation example, below is an example of simulating a
-- Crucible CFG generated from a Macaw function.  It assumes that the caller has
-- provided mappings from machine addresses to logical addresses, as well as
-- initial register and memory states (see Data.Macaw.Symbolic.Memory for an
-- example of constructing the mappings).
--
-- >>> :set -XFlexibleContexts
-- >>> :set -XImplicitParams
-- >>> :set -XOverloadedStrings
-- >>> :set -XScopedTypeVariables
-- >>> import           Data.IORef
-- >>> import qualified Data.Macaw.CFG as MC
-- >>> import qualified Data.Macaw.Symbolic as MS
-- >>> import qualified Lang.Crucible.Backend as CB
-- >>> import qualified Lang.Crucible.CFG.Core as CC
-- >>> import qualified Lang.Crucible.FunctionHandle as CFH
-- >>> import qualified Lang.Crucible.LLVM.MemModel as CLM
-- >>> import qualified Lang.Crucible.LLVM.Intrinsics as CLI
-- >>> import qualified Lang.Crucible.Simulator as CS
-- >>> import qualified Lang.Crucible.Simulator.GlobalState as CSG
-- >>> import qualified System.IO as IO
-- >>> :{
-- useCFG :: forall sym arch blocks
--         . (CB.IsSymInterface sym, MS.SymArchConstraints arch)
--        => CFH.HandleAllocator
--        -- ^ The handle allocator used to construct the CFG
--        -> sym
--        -- ^ The symbolic backend
--        -> MS.ArchVals arch
--        -- ^ 'ArchVals' from a prior call to 'archVals'
--        -> CS.RegMap sym (MS.MacawFunctionArgs arch)
--        -- ^ Initial register state for the simulation
--        -> CLM.MemImpl sym
--        -- ^ The initial memory state of the simulator
--        -> MS.GlobalMap sym MM.Mem (MC.ArchAddrWidth arch)
--        -- ^ A translator of machine code addresses to LLVM pointers
--        -> MS.LookupFunctionHandle sym arch
--        -- ^ A translator for machine code addresses to function handles
--        -> CC.CFG (MS.MacawExt arch) blocks (MS.MacawFunctionArgs arch) (MS.MacawFunctionResult arch)
--        -- ^ The CFG to simulate
--        -> IO ()
-- useCFG hdlAlloc sym avals initialRegs initialMem globalMap lfh cfg =
--   let ?recordLLVMAnnotation = \_ _ -> (pure () :: IO ())
--   in MS.withArchEval avals sym $ \archEvalFns -> do
--     let rep = CFH.handleReturnType (CC.cfgHandle cfg)
--     memModelVar <- CLM.mkMemVar "macaw:llvm_memory" hdlAlloc
--     -- For demonstration purposes, do not enforce any pointer validity constraints
--     -- See Data.Macaw.Symbolic.Memory for an example of a more sophisticated approach.
--     let mkValidityPred :: MkGlobalPointerValidityAssertion sym (M.ArchAddrWidth arch)
--         mkValidityPred _ _ _ _ = return Nothing
--     let extImpl = MS.macawExtensions archEvalFns memModelVar globalMap lfh mkValidityPred
--     let simCtx = CS.initSimContext sym CLI.llvmIntrinsicTypes hdlAlloc IO.stderr (CS.FnBindings CFH.emptyHandleMap) extImpl MS.MacawSimulatorState
--     let simGlobalState = CSG.insertGlobal memModelVar initialMem CS.emptyGlobals
--     let simulation = CS.regValue <$> CS.callCFG cfg initialRegs
--     let initialState = CS.InitialState simCtx simGlobalState CS.defaultAbortHandler rep (CS.runOverrideSim rep simulation)
--     let executionFeatures = []
--     execRes <- CS.executeCrucible executionFeatures initialState
--     case execRes of
--       CS.FinishedResult {} -> return ()
--       _ -> putStrLn "Simulation failed"
-- :}
