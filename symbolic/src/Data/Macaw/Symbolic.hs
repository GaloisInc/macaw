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
-- | The macaw-symbolic library translates Macaw functions (or blocks) into
-- Crucible CFGs for further analysis or symbolic execution.
--
-- This module (Data.Macaw.Symbolic) provides the entire user-facing API of the
-- library.  There are two main portions of the API:
--
-- 1. Translation of Macaw IR into Crucible CFGs
-- 2. Symbolic execution of Crucible CFGs generated from MAcaw
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
-- * Each function takes a single argument (the full set of machine registers)
--   and returns a single value (the full set of machine registers reflecting
--   any modifications)
module Data.Macaw.Symbolic
  ( ArchInfo(..)
  , ArchVals(..)
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
    -- ** Translating individual blocks
  , mkParsedBlockRegCFG
  , mkParsedBlockCFG
    -- ** Translating block paths
  , mkBlockPathRegCFG
  , mkBlockPathCFG
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
  -- ** The Macaw extension to Crucible
  , CG.MacawExt
  , CG.MacawExprExtension(..)
  , CG.MacawStmtExtension(..)
  , CG.MacawOverflowOp(..)
    -- * Simulating generated Crucible CFGs
    -- $simulationNotes
    -- $simulationExample
  , SymArchConstraints
  , macawExtensions
  , MO.GlobalMap
  , MO.LookupFunctionHandle(..)
  , MO.MacawSimulatorState(..)
    -- * Simplified entry points
  , runCodeBlock
  ) where

import           GHC.TypeLits

import           Control.Lens ((^.))
import           Control.Monad
import           Control.Monad.IO.Class
import           Control.Monad.ST (ST, RealWorld, stToIO)
import           Data.Foldable
import qualified Data.Map.Strict as Map
import           Data.Maybe
import           Data.Parameterized.Context (EmptyCtx, (::>), pattern Empty, pattern (:>))
import qualified Data.Parameterized.Context as Ctx
import           Data.Parameterized.Nonce ( NonceGenerator, newSTNonceGenerator )
import           Data.Parameterized.Some ( Some(Some) )
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Vector as V

import qualified What4.FunctionName as C
import           What4.Interface
import           What4.InterpretedFloatingPoint as C
import qualified What4.ProgramLoc as C
import           What4.Symbol (userSymbol)

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

import           System.IO (stdout)

import qualified Lang.Crucible.LLVM.MemModel as MM
import           Lang.Crucible.LLVM.Intrinsics (llvmIntrinsicTypes)

import qualified Data.Macaw.CFG.Block as M
import qualified Data.Macaw.CFG as M
import qualified Data.Macaw.Discovery.State as M
import qualified Data.Macaw.Types as M

import qualified Data.Macaw.Symbolic.Backend as SB
import           Data.Macaw.Symbolic.CrucGen as CG hiding (bvLit)
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
class ArchInfo arch where
  archVals :: proxy arch -> Maybe (ArchVals arch)

-- | The information to support use of macaw-symbolic for a given architecture
data ArchVals arch = ArchVals
  { archFunctions :: MacawSymbolicArchFunctions arch
  -- ^ This is the set of functions used by the translator, and is passed as the
  -- first argument to the translation functions (e.g., 'mkBlocksCFG').
  , withArchEval
      :: forall a m sym
       . (IsSymInterface sym, MonadIO m)
      => sym
      -> (SB.MacawArchEvalFn sym arch -> m a)
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
mkCrucRegCFG :: forall h arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible architecture-specific functions.
            -> C.HandleAllocator h
               -- ^ Handle allocator to make function handles
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> (forall s. MacawMonad arch ids h s (CR.Label s, [CR.Block (MacawExt arch) s (MacawFunctionResult arch)]))
                -- ^ Action to run
            -> ST h (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkCrucRegCFG archFns halloc nm action = do
  let crucRegTypes = crucArchRegTypes archFns
  let macawStructRepr = C.StructRepr crucRegTypes
  let argTypes = Empty :> macawStructRepr
  h <- C.mkHandle' halloc nm argTypes macawStructRepr
  Some (ng :: NonceGenerator (ST h) s) <- newSTNonceGenerator
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
addBlocksCFG :: forall h s arch ids
             .  MacawSymbolicArchFunctions arch
             -- ^ Crucible specific functions.
             -> MemSegmentMap (M.ArchAddrWidth arch)
             -- ^ Base address map
              -> M.ArchSegmentOff arch
                 -- ^ Address of start of block
             ->  (M.ArchAddrWord arch -> C.Position)
             -- ^ Function that maps offsets from start of block to Crucible position.
             -> [M.Block arch ids]
             -- ^ List of blocks for this region.
             -> MacawMonad arch ids h s (CR.Label s, [CR.Block (MacawExt arch) s (MacawFunctionResult arch)])
addBlocksCFG archFns baseAddrMap addr posFn macawBlocks = do
  crucGenArchConstraints archFns $ do
   -- Map block map to Crucible CFG
  blockLabelMap <- fmap Map.fromList $ sequence $
                     [ mmFreshNonce >>= \n -> return (w, CR.Label n)
                     | w <- M.blockLabel <$> macawBlocks ]
  entry <-
    case Map.lookup 0 blockLabelMap of
      Just lbl -> return lbl
      Nothing -> fail "Unable to find initial block"
  blks <- forM macawBlocks $ \b -> do
    addMacawBlock archFns baseAddrMap addr blockLabelMap posFn b
  return (entry, concatMap (uncurry (:)) blks)

-- | Create a registerized Crucible CFG from an arbitrary list of macaw blocks
--
-- Note that this variant takes macaw 'M.Block' blocks - these are blocks as
-- returned from the architecture-specific disassembler and are /not/ the parsed
-- blocks returned by the code discovery (i.e., not those found in
-- 'M.DiscoveryFunInfo').
--
-- Also note that any 'M.FetchAndExecute' terminators are turned into Crucible
-- return statements.
mkBlocksRegCFG :: forall s arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible specific functions.
            -> C.HandleAllocator s
               -- ^ Handle allocator to make the blocks
            -> MemSegmentMap (M.ArchAddrWidth arch)
               -- ^ Map from region indices to their address
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> M.ArchSegmentOff arch
               -- ^ Address for start of block.
            -> (M.ArchAddrWord arch -> C.Position)
            -- ^ Function that maps offsets from start of block to Crucible position.
            -> [M.Block arch ids]
            -- ^ List of blocks for this region.
            -> ST s (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlocksRegCFG archFns halloc memBaseVarMap nm addr posFn macawBlocks = do
  mkCrucRegCFG archFns halloc nm $ do
    addBlocksCFG archFns memBaseVarMap addr posFn macawBlocks

-- | Create a Crucible CFG from an arbitrary list of macaw blocks
--
-- Note that this variant takes macaw 'M.Block' blocks - these are blocks as
-- returned from the architecture-specific disassembler and are /not/ the parsed
-- blocks returned by the code discovery (i.e., not those found in
-- 'M.DiscoveryFunInfo').
--
-- Also note that any 'M.FetchAndExecute' terminators are turned into Crucible
-- return statements.
mkBlocksCFG :: forall s arch ids
            .  MacawSymbolicArchFunctions arch
               -- ^ Crucible specific functions.
            -> C.HandleAllocator s
               -- ^ Handle allocator to make the blocks
            -> MemSegmentMap (M.ArchAddrWidth arch)
               -- ^ Map from region indices to their address
            -> C.FunctionName
               -- ^ Name of function for pretty print purposes.
            -> M.ArchSegmentOff arch
               -- ^ Address for start of block.
            -> (M.ArchAddrWord arch -> C.Position)
            -- ^ Function that maps offsets from start of block to Crucible position.
            -> [M.Block arch ids]
            -- ^ List of blocks for this region.
            -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlocksCFG archFns halloc memBaseVarMap nm addr posFn macawBlocks =
  toCoreCFG archFns <$>
  mkBlocksRegCFG archFns halloc memBaseVarMap nm addr posFn macawBlocks

-- | Create a map from Macaw @(address, index)@ pairs to Crucible labels
mkBlockLabelMap :: [M.ParsedBlock arch ids] -> MacawMonad arch ids h s (BlockLabelMap arch s)
mkBlockLabelMap blks = foldM insBlock Map.empty blks
 where insBlock :: BlockLabelMap arch s -> M.ParsedBlock arch ids -> MacawMonad arch ids h s (BlockLabelMap arch s)
       insBlock m b = insSentences (M.pblockAddr b) m [M.blockStatementList b]

       insSentences :: M.ArchSegmentOff arch
                    -> (BlockLabelMap arch s)
                    -> [M.StatementList arch ids]
                    -> MacawMonad arch ids h s (BlockLabelMap arch s)
       insSentences _ m [] = return m
       insSentences base m (s:r) = do
         n <- mmFreshNonce
         insSentences base
                      (Map.insert (base,M.stmtsIdent s) (CR.Label n) m)
                      (nextStatements (M.stmtsTerm s) ++ r)

-- | Normalise any term statements to returns --- i.e., remove branching, jumping, etc.
--
-- This is used when translating a single Macaw block into Crucible, as Crucible
-- functions must end in a return.
termStmtToReturn :: forall arch ids. M.StatementList arch ids -> M.StatementList arch ids
termStmtToReturn sl = sl { M.stmtsTerm = tm }
  where
    tm :: M.ParsedTermStmt arch ids
    tm = case M.stmtsTerm sl of
      tm0@M.ParsedReturn{} -> tm0
      M.ParsedCall r _ -> M.ParsedReturn r
      M.ParsedJump r _ -> M.ParsedReturn r
      M.ParsedLookupTable r _ _ -> M.ParsedReturn r
      M.ParsedIte b l r -> M.ParsedIte b (termStmtToReturn l) (termStmtToReturn r)
      M.ParsedArchTermStmt _ r _ -> M.ParsedReturn r
      M.ClassifyFailure r -> M.ParsedReturn r
      tm0@M.PLTStub{} -> tm0
      tm0@M.ParsedTranslateError{} -> tm0

-- | Normalise any term statements to jumps.
termStmtToJump
  :: forall arch ids
   . M.StatementList arch ids
  -> M.ArchSegmentOff arch
  -> M.StatementList arch ids
termStmtToJump sl addr = sl { M.stmtsTerm = tm }
  where
    tm :: M.ParsedTermStmt arch ids
    tm = case M.stmtsTerm sl of
      M.ParsedJump r _ -> M.ParsedJump r addr
      M.ParsedCall r _ -> M.ParsedJump r addr
      M.ParsedReturn r -> M.ParsedJump r addr
      M.ParsedLookupTable r _ _ -> M.ParsedJump r addr
      M.ParsedIte b l r ->
        M.ParsedIte b (termStmtToJump l addr) (termStmtToJump r addr)
      M.ParsedArchTermStmt _ r _ -> M.ParsedJump r addr
      M.ClassifyFailure r -> M.ParsedJump r addr
      tm0@M.PLTStub{} -> tm0
      tm0@M.ParsedTranslateError{} -> tm0

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
mkParsedBlockRegCFG :: forall h arch ids
                 .  MacawSymbolicArchFunctions arch
                 -- ^ Architecture specific functions.
                 -> C.HandleAllocator h
                 -- ^ Handle allocator to make the blocks
                 -> MemSegmentMap (M.ArchAddrWidth arch)
                 -- ^ Map from region indices to their address
                 -> (M.ArchSegmentOff arch -> C.Position)
                 -- ^ Function that maps function address to Crucible position
                 -> M.ParsedBlock arch ids
                 -- ^ Block to translate
                 -> ST h (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkParsedBlockRegCFG archFns halloc memBaseVarMap posFn b = crucGenArchConstraints archFns $ do
  mkCrucRegCFG archFns halloc "" $ do
    let strippedBlock = b { M.blockStatementList = termStmtToReturn (M.blockStatementList b) }

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
    inputAtom <- mmExecST $ CR.mkInputAtoms ng entryPos (Empty :> regType) >>= \case
      Empty :> atm -> return atm
      _ -> error "Invalid input atom creation for mkParsedBlockRegCFG"
    -- Create map from Macaw (address,blockId pairs) to Crucible labels
    blockLabelMap :: BlockLabelMap arch s <-
      mkBlockLabelMap [strippedBlock]

    -- Get initial block for Crucible
    entryLabel <- CR.Label <$> mmFreshNonce
    let initPosFn :: M.ArchAddrWord arch -> C.Position
        initPosFn off = posFn r
          where Just r = M.incSegmentOff entryAddr (toInteger off)
    (initCrucibleBlock,initExtraCrucibleBlocks,_) <-
      runCrucGen archFns memBaseVarMap initPosFn 0 entryLabel regReg $ do
        -- Initialize value in regReg with initial registers
        setMachineRegs inputAtom
        -- Jump to function entry point
        addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap entryAddr 0)

    -- Generate code for Macaw block after entry
    crucibleBlock <- addParsedBlock archFns memBaseVarMap blockLabelMap posFn regReg strippedBlock

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
mkParsedBlockCFG :: forall s arch ids
                 .  MacawSymbolicArchFunctions arch
                 -- ^ Architecture specific functions.
                 -> C.HandleAllocator s
                 -- ^ Handle allocator to make the blocks
                 -> MemSegmentMap (M.ArchAddrWidth arch)
                 -- ^ Map from region indices to their address
                 -> (M.ArchSegmentOff arch -> C.Position)
                 -- ^ Function that maps function address to Crucible position
                 -> M.ParsedBlock arch ids
                 -- ^ Block to translate
                 -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkParsedBlockCFG archFns halloc memBaseVarMap posFn b =
  toCoreCFG archFns <$> mkParsedBlockRegCFG archFns halloc memBaseVarMap posFn b

mkBlockPathRegCFG
  :: forall h arch ids
   . MacawSymbolicArchFunctions arch
  -- ^ Architecture specific functions.
  -> C.HandleAllocator h
  -- ^ Handle allocator to make the blocks
  -> MemSegmentMap (M.ArchAddrWidth arch)
  -- ^ Map from region indices to their address
  -> (M.ArchSegmentOff arch -> C.Position)
  -- ^ Function that maps function address to Crucible position
  -> [M.ParsedBlock arch ids]
  -- ^ Bloc path to translate
  -> ST h (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlockPathRegCFG arch_fns halloc mem_base_var_map pos_fn blocks =
  crucGenArchConstraints arch_fns $ mkCrucRegCFG arch_fns halloc "" $ do
    let entry_addr = M.pblockAddr $ head blocks
    let first_blocks = zipWith
          (\block next_block ->
            block { M.blockStatementList = termStmtToJump (M.blockStatementList block) (M.pblockAddr next_block) })
          (take (length blocks - 1) blocks)
          (tail blocks)
    let last_block = (last blocks) { M.blockStatementList = termStmtToReturn (M.blockStatementList (last blocks)) }
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

    let off_pos_fn :: M.ArchSegmentOff arch -> M.ArchAddrWord arch -> C.Position
        off_pos_fn base = pos_fn . fromJust . M.incSegmentOff base . toInteger

    let runCrucGen' addr label = runCrucGen
          arch_fns
          mem_base_var_map
          (off_pos_fn addr)
          0
          label
          arch_reg_struct_reg

    -- Generate entry Crucible block
    entry_label <- CR.Label <$> mmFreshNonce
    (init_crucible_block, init_extra_crucible_blocks, _) <-
      runCrucGen' entry_addr entry_label $ do
        -- Initialize value in arch_reg_struct_reg with initial registers
        setMachineRegs input_atom
        -- Jump to function entry point
        addTermStmt $ CR.Jump (parsedBlockLabel block_label_map entry_addr 0)

    -- Generate code for Macaw blocks
    crucible_blocks <- forM block_path $ \block -> do
      let block_addr = M.pblockAddr block
      let stmts = M.blockStatementList block
      let label = block_label_map Map.! (block_addr, M.stmtsIdent stmts)

      (first_crucible_block, first_extra_crucible_blocks, off) <- runCrucGen' block_addr label $ do
        arch_width <- archAddrWidth
        ip_reg_val <- getRegValue M.ip_reg
        block_ptr <- evalMacawStmt $
          MacawGlobalPtr arch_width $ M.segoffAddr block_addr
        cond <- evalMacawStmt $ PtrEq arch_width ip_reg_val block_ptr
        msg <- appAtom $ C.TextLit
          "the current block follows the previous block in the path"
        addStmt $ CR.Assume cond msg

        mapM_ (addMacawStmt block_addr) (M.stmtsNonterm stmts)
        addMacawParsedTermStmt block_label_map block_addr (M.stmtsTerm stmts)

      let next_stmts = map ((,) off) $ nextStatements $ M.stmtsTerm stmts
      addStatementList
        arch_fns
        mem_base_var_map
        block_label_map
        block_addr
        (off_pos_fn block_addr)
        arch_reg_struct_reg
        next_stmts
        (first_crucible_block:first_extra_crucible_blocks)

    pure (entry_label, init_crucible_block :
                         init_extra_crucible_blocks ++ concat crucible_blocks)

mkBlockPathCFG
  :: forall s arch ids
   . MacawSymbolicArchFunctions arch
  -- ^ Architecture specific functions.
  -> C.HandleAllocator s
  -- ^ Handle allocator to make the blocks
  -> MemSegmentMap (M.ArchAddrWidth arch)
  -- ^ Map from region indices to their address
  -> (M.ArchSegmentOff arch -> C.Position)
  -- ^ Function that maps function address to Crucible position
  -> [M.ParsedBlock arch ids]
  -- ^ Block to translate
  -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkBlockPathCFG arch_fns halloc mem_base_var_map pos_fn blocks =
  toCoreCFG arch_fns <$>
    mkBlockPathRegCFG arch_fns halloc mem_base_var_map pos_fn blocks

-- | Translate a macaw function (passed as a 'M.DiscoveryFunInfo') into a
-- registerized Crucible CFG
--
-- This is provided as an alternative to 'mkFunCFG' to allow for post-processing
-- of the CFG (e.g., instrumentation) prior to the SSA conversion (which can be
-- done using 'toCoreCFG').
mkFunRegCFG :: forall h arch ids
         .  MacawSymbolicArchFunctions arch
            -- ^ Architecture specific functions.
         -> C.HandleAllocator h
            -- ^ Handle allocator to make the blocks
         -> MemSegmentMap (M.ArchAddrWidth arch)
            -- ^ Map from region indices to their address
         -> C.FunctionName
            -- ^ Name of function for pretty print purposes.
         -> (M.ArchSegmentOff arch -> C.Position)
            -- ^ Function that maps function address to Crucible position
         -> M.DiscoveryFunInfo arch ids
         -- ^ List of blocks for this region.
         -> ST h (CR.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkFunRegCFG archFns halloc memBaseVarMap nm posFn fn = crucGenArchConstraints archFns $ do
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
    inputAtom <- mmExecST $ CR.mkInputAtoms ng entryPos (Empty :> regType) >>= \case
      Empty :> atm -> return atm
      _ -> error "Error creating input atom for mkFunRegCFG"
    -- Create map from Macaw (address,blockId pairs) to Crucible labels
    blockLabelMap :: BlockLabelMap arch s <-
      mkBlockLabelMap blockList
    -- Get initial block for Crucible
    entryLabel <- CR.Label <$> mmFreshNonce
    let initPosFn :: M.ArchAddrWord arch -> C.Position
        initPosFn off = posFn r
          where Just r = M.incSegmentOff entryAddr (toInteger off)
    (initCrucibleBlock,initExtraCrucibleBlocks,_) <-
      runCrucGen archFns memBaseVarMap initPosFn 0 entryLabel regReg $ do
        -- Initialize value in regReg with initial registers
        setMachineRegs inputAtom
        -- Jump to function entry point
        addTermStmt $ CR.Jump (parsedBlockLabel blockLabelMap entryAddr 0)

    -- Generate code for Macaw blocks after entry
    restCrucibleBlocks <-
      forM blockList $ \b -> do
        addParsedBlock archFns memBaseVarMap blockLabelMap posFn regReg b
    -- Return initialization block followed by actual blocks.
    pure (entryLabel, initCrucibleBlock :
                        initExtraCrucibleBlocks ++ concat restCrucibleBlocks)

-- | Translate a macaw function (passed as a 'M.DiscoveryFunInfo') into a Crucible 'C.CFG' (in SSA form)
mkFunCFG :: forall s arch ids
         .  MacawSymbolicArchFunctions arch
            -- ^ Architecture specific functions.
         -> C.HandleAllocator s
            -- ^ Handle allocator to make the blocks
         -> MemSegmentMap (M.ArchAddrWidth arch)
            -- ^ Map from region indices to their address
         -> C.FunctionName
            -- ^ Name of function for pretty print purposes.
         -> (M.ArchSegmentOff arch -> C.Position)
            -- ^ Function that maps function address to Crucible position
         -> M.DiscoveryFunInfo arch ids
            -- ^ List of blocks for this region.
         -> ST s (C.SomeCFG (MacawExt arch) (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch))
mkFunCFG archFns halloc memBaseVarMap nm posFn fn =
  toCoreCFG archFns <$> mkFunRegCFG archFns halloc memBaseVarMap nm posFn fn

-- | Generate the final SSA CFG from a registerized CFG. Offered
-- separately in case post-processing on the registerized CFG is
-- desired.
toCoreCFG :: MacawSymbolicArchFunctions arch
          -> CR.SomeCFG (MacawExt arch) init ret
          -- ^ A registerized Crucible CFG
          -> C.SomeCFG (MacawExt arch) init ret
toCoreCFG archFns (CR.SomeCFG cfg) = crucGenArchConstraints archFns $ C.toSSA cfg

-- * Symbolic simulation


plus1LeqDbl :: forall n w . (2 <= n, 1 <= w) => NatRepr n -> NatRepr w -> LeqProof (w+1) (n * w)
plus1LeqDbl n w =
  case testLeq (incNat w) (natMultiply n w) of
    Nothing -> error "Unexpected vector"
    Just p -> p

checkMacawFloatEq :: M.FloatInfoRepr ftp
                  -> FloatInfoToBitWidth (ToCrucibleFloatInfo ftp) :~: M.FloatInfoBits ftp
checkMacawFloatEq f =
  case f of
    M.SingleFloatRepr -> Refl
    M.HalfFloatRepr   -> Refl
    M.DoubleFloatRepr -> Refl
    M.QuadFloatRepr   -> Refl
    M.X86_80FloatRepr -> Refl


doBitcast :: forall sym i o
          .  IsSymInterface sym
          => sym
          -> C.RegValue sym (ToCrucibleType i)
          -> M.WidthEqProof i o
          -> IO (C.RegValue sym (ToCrucibleType o))
doBitcast sym x eqPr =
  case eqPr of
    M.PackBits (n :: NatRepr n) (w :: NatRepr w) -> do
      let outW = natMultiply n w
      LeqProof <- pure $ leqMulPos n w
      LeqProof <- pure $ plus1LeqDbl n w
      when (fromIntegral (V.length x) /= natValue n) $ do
        fail "bitcast: Incorrect input vector length"
      -- We should have at least one element due to constraint on n
      let Just h = x V.!? 0
      let rest :: V.Vector (MM.LLVMPtr sym w)
          rest = V.tail x
      extH <- bvZext sym outW =<< MM.projectLLVM_bv sym h
      let doPack :: (Integer,SymBV sym (n*w)) -> MM.LLVMPtr sym w -> IO (Integer, SymBV sym (n*w))
          doPack (i,r) y = do
            extY <- bvZext sym outW =<< MM.projectLLVM_bv sym y
            shiftAmt <- bvLit sym outW i
            r' <- bvOrBits sym r =<< bvShl sym extY shiftAmt
            pure (i+1,r')
      (_,r) <- foldlM doPack (1,extH) rest
      MM.llvmPointer_bv sym r
    M.UnpackBits n w -> do
      let inW = natMultiply n w
      LeqProof <- pure $ leqMulPos n w
      LeqProof <- pure $ plus1LeqDbl n w
      xbv <- MM.projectLLVM_bv sym x
      V.generateM (fromIntegral (natValue n)) $ \i -> do
        shiftAmt <- bvLit sym inW (toInteger i)
        MM.llvmPointer_bv sym =<< bvTrunc sym w =<< bvLshr sym xbv shiftAmt
    M.FromFloat f -> do
      Refl <- pure $ checkMacawFloatEq f
      xbv <- C.iFloatToBinary sym (floatInfoToCrucible f) x
      MM.llvmPointer_bv sym xbv
    M.ToFloat f -> do
      xbv <- MM.projectLLVM_bv sym x
      Refl <- pure $ checkMacawFloatEq f
      C.iFloatFromBinary sym (floatInfoToCrucible f) xbv
    M.VecEqCongruence _n eltPr -> do
      forM x $ \e -> doBitcast sym e eltPr

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
      one  <- What4.Interface.bvLit sym w' 1
      zero <- What4.Interface.bvLit sym w' 0
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

-- | This evaluates a  Macaw statement extension in the simulator.
execMacawStmtExtension
  :: forall sym arch
  . (IsSymInterface sym)
  => SB.MacawArchEvalFn sym arch
  -- ^ Simulation-time interpretations of architecture-specific functions
  -> C.GlobalVar MM.Mem
  -- ^ The distinguished global variable holding the current state of the memory model
  -> MO.GlobalMap sym (M.ArchAddrWidth arch)
  -- ^ The translation from machine words to LLVM memory model pointers
  -> MO.LookupFunctionHandle sym arch
  -- ^ A function to turn machine addresses into Crucible function
  -- handles (which can also perform lazy CFG creation)
  -> SB.EvalStmtFunc (MacawStmtExtension arch) (MacawSimulatorState sym) sym (MacawExt arch)
execMacawStmtExtension (SB.MacawArchEvalFn archStmtFn) mvar globs (MO.LookupFunctionHandle lookupH) s0 st =
  case s0 of
    MacawReadMem addrWidth memRep ptr0 -> do
      let sym = st^.C.stateSymInterface
      mem <- getMem st mvar
      ptr <- tryGlobPtr sym mem globs (C.regValue ptr0)
      (,st) <$> doReadMem sym mem addrWidth memRep ptr
    MacawCondReadMem addrWidth memRep cond ptr0 condFalseValue -> do
      let sym = st^.C.stateSymInterface
      mem <- getMem st mvar
      ptr <- tryGlobPtr sym mem globs (C.regValue ptr0)
      (,st) <$> doCondReadMem sym mem addrWidth memRep (C.regValue cond) ptr (C.regValue condFalseValue)
    MacawWriteMem addrWidth memRep ptr0 v -> do
      let sym = st^.C.stateSymInterface
      mem <- getMem st mvar
      ptr <- tryGlobPtr sym mem globs (C.regValue ptr0)
      mem1 <- doWriteMem sym mem addrWidth memRep ptr (C.regValue v)
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


-- | Return macaw extension evaluation functions.
macawExtensions
  :: IsSymInterface sym
  => SB.MacawArchEvalFn sym arch
  -- ^ A set of interpretations for architecture-specific functions
  -> C.GlobalVar MM.Mem
  -- ^ The Crucible global variable containing the current state of the memory
  -- model
  -> GlobalMap sym (M.ArchAddrWidth arch)
  -- ^ A function that maps bitvectors to valid memory model pointers
  -> LookupFunctionHandle sym arch
  -- ^ A function to translate virtual addresses into function handles
  -- dynamically during symbolic execution
  -> C.ExtensionImpl (MacawSimulatorState sym) sym (MacawExt arch)
macawExtensions f mvar globs lookupH =
  C.ExtensionImpl { C.extensionEval = evalMacawExprExtension
                  , C.extensionExec = execMacawStmtExtension f mvar globs lookupH
                  }

-- | Run the simulator over a contiguous set of code.
runCodeBlock
  :: forall sym arch blocks
   . (C.IsSyntaxExtension (MacawExt arch), IsSymInterface sym)
  => sym
  -> MacawSymbolicArchFunctions arch
  -- ^ Translation functions
  -> SB.MacawArchEvalFn sym arch
  -> C.HandleAllocator RealWorld
  -> (MM.MemImpl sym, GlobalMap sym (M.ArchAddrWidth arch))
  -> LookupFunctionHandle sym arch
  -> C.CFG (MacawExt arch) blocks (EmptyCtx ::> ArchRegStruct arch) (ArchRegStruct arch)
  -> Ctx.Assignment (C.RegValue' sym) (MacawCrucibleRegTypes arch)
  -- ^ Register assignment
  -> IO ( C.GlobalVar MM.Mem
        , C.ExecResult
          (MacawSimulatorState sym)
          sym
          (MacawExt arch)
          (C.RegEntry sym (ArchRegStruct arch)))
runCodeBlock sym archFns archEval halloc (initMem,globs) lookupH g regStruct = do
  mvar <- stToIO (MM.mkMemVar halloc)
  let crucRegTypes = crucArchRegTypes archFns
  let macawStructRepr = C.StructRepr crucRegTypes

  let ctx :: C.SimContext (MacawSimulatorState sym) sym (MacawExt arch)
      ctx = let fnBindings = C.insertHandleMap (C.cfgHandle g)
                             (C.UseCFG g (C.postdomInfo g)) $
                             C.emptyHandleMap
                extImpl = macawExtensions archEval mvar globs lookupH
            in C.initSimContext sym llvmIntrinsicTypes halloc stdout
               fnBindings extImpl MacawSimulatorState
  -- Create the symbolic simulator state
  let initGlobals = C.insertGlobal mvar initMem C.emptyGlobals
  let s = C.InitialState ctx initGlobals C.defaultAbortHandler $
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
-- > {-# LANGUAGE FlexibleContexts #-}
-- > {-# LANGUAGE ScopedTypeVariables #-}
-- > {-# LANGUAGE TypeApplications #-}
-- > import           Control.Monad.ST ( stToIO )
-- > import qualified Data.Macaw.CFG as MC
-- > import qualified Data.Macaw.Discovery as MD
-- > import qualified Data.Macaw.Symbolic as MS
-- > import qualified Data.Map as Map
-- > import           Data.Proxy ( Proxy(..) )
-- > import qualified Data.Text.Encoding as TE
-- > import qualified Data.Text.Encoding.Error as TEE
-- > import qualified Lang.Crucible.CFG.Core as CC
-- > import qualified Lang.Crucible.FunctionHandle as CFH
-- > import qualified What4.FunctionName as WFN
-- > import qualified What4.ProgramLoc as WPL
-- >
-- > translate :: forall arch ids
-- >            . (MS.ArchInfo arch, MC.MemWidth (MC.ArchAddrWidth arch))
-- >           => MD.DiscoveryFunInfo arch ids
-- >           -> IO ()
-- > translate dfi =
-- >   case MS.archVals (Proxy @arch) of
-- >     Nothing -> putStrLn "Architecture does not support symbolic reasoning"
-- >     Just MS.ArchVals { MS.archFunctions = archFns } -> do
-- >       hdlAlloc <- CFH.newHandleAllocator
-- >       let nameText = TE.decodeUtf8With TEE.lenientDecode (MD.discoveredFunName dfi)
-- >       let name = WFN.functionNameFromText nameText
-- >       let posFn addr = WPL.BinaryPos nameText (maybe 0 fromIntegral (MC.segoffAsAbsoluteAddr addr))
-- >       cfg <- stToIO $ MS.mkFunCFG archFns hdlAlloc Map.empty name posFn dfi
-- >       useCFG cfg
-- >
-- > useCFG :: CC.SomeCFG (MS.MacawExt arch) (MS.MacawFunctionArgs arch) (MS.MacawFunctionResult arch) -> IO ()
-- > useCFG _ = return ()
-- >

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
-- > {-# LANGUAGE FlexibleContexts #-}
-- > import           Control.Monad.ST ( stToIO, RealWorld )
-- > import qualified Data.Macaw.CFG as MC
-- > import qualified Data.Macaw.Symbolic as MS
-- > import qualified Lang.Crucible.Backend as CB
-- > import qualified Lang.Crucible.CFG.Core as CC
-- > import qualified Lang.Crucible.FunctionHandle as CFH
-- > import qualified Lang.Crucible.LLVM.MemModel as CLM
-- > import qualified Lang.Crucible.LLVM.Intrinsics as CLI
-- > import qualified Lang.Crucible.Simulator as CS
-- > import qualified Lang.Crucible.Simulator.GlobalState as CSG
-- > import qualified System.IO as IO
-- >
-- > useCFG :: (CB.IsSymInterface sym, MS.SymArchConstraints arch)
-- >        => CFH.HandleAllocator RealWorld
-- >        -- ^ The handle allocator used to construct the CFG
-- >        -> sym
-- >        -- ^ The symbolic backend
-- >        -> MS.ArchVals arch
-- >        -- ^ 'ArchVals' from a prior call to 'archVals'
-- >        -> CS.RegMap sym (MS.MacawFunctionArgs arch)
-- >        -- ^ Initial register state for the simulation
-- >        -> CLM.MemImpl sym
-- >        -- ^ The initial memory state of the simulator
-- >        -> MS.GlobalMap sym (MC.ArchAddrWidth arch)
-- >        -- ^ A translator of machine code addresses to LLVM pointers
-- >        -> MS.LookupFunctionHandle sym arch
-- >        -- ^ A translator for machine code addresses to function handles
-- >        -> CC.CFG (MS.MacawExt arch) blocks (MS.MacawFunctionArgs arch) (MS.MacawFunctionResult arch)
-- >        -- ^ The CFG to simulate
-- >        -> IO ()
-- > useCFG hdlAlloc sym MS.ArchVals { MS.withArchEval = withArchEval }
-- >        initialRegs initialMem globalMap lfh cfg = withArchEval sym $ \archEvalFns -> do
-- >   let rep = CFH.handleReturnType (CC.cfgHandle cfg)
-- >   memModelVar <- stToIO (CLM.mkMemVar hdlAlloc)
-- >   let extImpl = MS.macawExtensions archEvalFns memModelVar globalMap lfh
-- >   let simCtx = CS.initSimContext sym CLI.llvmIntrinsicTypes hdlAlloc IO.stderr CFH.emptyHandleMap extImpl MS.MacawSimulatorState
-- >   let simGlobalState = CSG.insertGlobal memModelVar initialMem CS.emptyGlobals
-- >   let simulation = CS.regValue <$> CS.callCFG cfg initialRegs
-- >   let initialState = CS.InitialState simCtx simGlobalState CS.defaultAbortHandler (CS.runOverrideSim rep simulation)
-- >   let executionFeatures = []
-- >   execRes <- CS.executeCrucible executionFeatures initialState
-- >   case execRes of
-- >     CS.FinishedResult {} -> return ()
-- >     _ -> putStrLn "Simulation failed"
-- >
