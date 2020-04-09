{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.ARM.Arch where

import           Data.Bits ( (.&.) )
import           Data.Kind ( Type )
import qualified Data.Macaw.Architecture.Info as MAI
import           Data.Macaw.ARM.ARMReg ()
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MCB
import           Data.Macaw.CFG.Rewriter ( Rewriter, rewriteValue, appendRewrittenArchStmt
                                         , evalRewrittenArchFn )
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FCls
import qualified Data.Word.Indexed as WI
import qualified Dismantle.ARM.A32 as ARMDis
import qualified Dismantle.ARM.T32 as ThumbDis
import           GHC.TypeLits
import qualified SemMC.Architecture.AArch32 as ARM
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Text.PrettyPrint.HughesPJClass as HPP

-- ----------------------------------------------------------------------
-- ARM-specific statement definitions

data ARMStmt (v :: MT.Type -> Type) where

type instance MC.ArchStmt ARM.AArch32 = ARMStmt

instance MC.IsArchStmt ARMStmt where
    ppArchStmt _pp stmt =
        case stmt of

instance TF.FunctorF ARMStmt where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ARMStmt where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ARMStmt where
  traverseF _go stmt =
    case stmt of

rewriteStmt :: ARMStmt (MC.Value ARM.AArch32 src) -> Rewriter ARM.AArch32 s src tgt ()
rewriteStmt s = appendRewrittenArchStmt =<< TF.traverseF rewriteValue s

-- The ArchBlockPrecond type holds data required for an architecture to compute
-- new abstract states at the beginning on a block.  PowerPC doesn't need any
-- additional information, so we use ()
type instance MAI.ArchBlockPrecond ARM.AArch32 = ()

-- ----------------------------------------------------------------------
-- ARM terminal statements (which have instruction-specific effects on
-- control-flow and register state).

data ARMTermStmt ids where
  ARMSyscall :: WI.W 24 -> ARMTermStmt ids
    -- ThumbSyscall :: ThumbDis.Operand "Imm0_255" -> ARMTermStmt ids

deriving instance Show (ARMTermStmt ids)

type instance MC.ArchTermStmt ARM.AArch32 = ARMTermStmt

instance MC.PrettyF ARMTermStmt where
  prettyF ts = let dpp2app :: forall a. HPP.Pretty a => a -> PP.Doc
                   dpp2app = PP.text . show . HPP.pPrint
               in case ts of
                    ARMSyscall imm -> PP.text "arm_syscall" PP.<+> dpp2app imm

rewriteTermStmt :: ARMTermStmt src -> Rewriter ARM.AArch32 s src tgt (ARMTermStmt tgt)
rewriteTermStmt s =
    case s of
      ARMSyscall imm -> pure $ ARMSyscall imm

-- ----------------------------------------------------------------------
-- ARM functions.  These may return a value, and may depend on the
-- current state of the heap and the set of registeres defined so far
-- and the result type, but should not affect the processor state.

data ARMPrimFn (f :: MT.Type -> Type) tp where
  SDiv :: 1 <= w => NR.NatRepr w
       -> f (MT.BVType w)
       -> f (MT.BVType w)
       -> ARMPrimFn f (MT.BVType w)
  UDiv :: 1 <= w => NR.NatRepr w
       -> f (MT.BVType w)
       -> f (MT.BVType w)
       -> ARMPrimFn f (MT.BVType w)
  SRem :: 1 <= w => NR.NatRepr w
       -> f (MT.BVType w)
       -> f (MT.BVType w)
       -> ARMPrimFn f (MT.BVType w)
  URem :: 1 <= w => NR.NatRepr w
       -> f (MT.BVType w)
       -> f (MT.BVType w)
       -> ARMPrimFn f (MT.BVType w)

instance MC.IsArchFn ARMPrimFn where
    ppArchFn pp f =
        let ppBinary s v1' v2' = PP.text s PP.<+> v1' PP.<+> v2'
        in case f of
          UDiv _ lhs rhs -> ppBinary "arm_udiv" <$> pp lhs <*> pp rhs
          SDiv _ lhs rhs -> ppBinary "arm_sdiv" <$> pp lhs <*> pp rhs
          URem _ lhs rhs -> ppBinary "arm_urem" <$> pp lhs <*> pp rhs
          SRem _ lhs rhs -> ppBinary "arm_srem" <$> pp lhs <*> pp rhs

instance FCls.FunctorFC ARMPrimFn where
  fmapFC = FCls.fmapFCDefault

instance FCls.FoldableFC ARMPrimFn where
  foldMapFC = FCls.foldMapFCDefault

instance FCls.TraversableFC ARMPrimFn where
  traverseFC go f =
    case f of
      UDiv rep lhs rhs -> UDiv rep <$> go lhs <*> go rhs
      SDiv rep lhs rhs -> SDiv rep <$> go lhs <*> go rhs
      URem rep lhs rhs -> URem rep <$> go lhs <*> go rhs
      SRem rep lhs rhs -> SRem rep <$> go lhs <*> go rhs

type instance MC.ArchFn ARM.AArch32 = ARMPrimFn

instance MT.HasRepr (ARMPrimFn (MC.Value ARM.AArch32 ids)) MT.TypeRepr where
  typeRepr f =
    case f of
      UDiv rep _ _ -> MT.BVTypeRepr rep
      SDiv rep _ _ -> MT.BVTypeRepr rep
      URem rep _ _ -> MT.BVTypeRepr rep
      SRem rep _ _ -> MT.BVTypeRepr rep

instance MC.IPAlignment ARM.AArch32 where
  -- A formula which results in an address that will be loaded into
  -- the IP (PC) masks the lower bits based on the current and target
  -- mode.  See bxWritePC for more details.  The fromIPAligned
  -- attempts to recognize these formulas and remove the part of the
  -- formula that performs the masking/adjustment.
  --
  -- This current implementation is not fully correct (notably the
  -- current and target state are not known), but at present it is
  -- thought that it will suffice based on the following assumptions:
  --
  --   1. The expectation is that these are only used when working
  --      with values that would be loaded into the PC, so recognizing
  --      all forms of the bxWritePC/maskPCForSubArch manipulation
  --      (see
  --      SemMC.Architecture.ARM.BaseSemantics.Pseudocode.Registers)
  --      of the PC value should be correct enough without necessarily
  --      knowing what the current ITSTATE is (A32 or T32 or other).
  --
  --   2. That this will not generally be used for general equations
  --      whose target is not the IP (PC).
  --
  --   3. That the current instruction is one that has these specific
  --      effects on writing to the PC (see "Writing to the PC" on
  --      Page E1-2295).
  --
  fromIPAligned cleanedAddrVal
    | Just (MC.BVAnd _ mask dirtyAddrVal) <- MC.valueAsApp cleanedAddrVal
    , MC.BVValue natS v <- mask
    , s <- natVal natS
    = if v `elem` [ ((2^s) - 1) - 1  -- bxWritePC toT32
                  , ((2^s) - 1) - 2  -- bxWritePC !toT32, branchWritePC T32, branchWritePCRel T32
                  , ((2^s) - 1) - 3  -- branchWritePC A32, branchWritePCRel A32
                  ]
      then Just dirtyAddrVal else Nothing
    | otherwise = Nothing

  toIPAligned addrVal =
    -- Optimally, the conversion of a generic MemoryAddr into a
    -- suitable IP/PC value would mask based on the current InstrSet
    -- state (A32 masking 0b11 or T32 masking 0b01), but at present
    -- the current InstrSet is not known.  Since the current use of
    -- 'toIPAligned' is on addresses that are generally taken from
    -- jumptables, and these are not usually stocked with unaligned
    -- addresses, so the current implementation just performs the
    -- minimal common functionality in the hopes that it will be
    -- sufficient.
    let mask = 0b01
    in addrVal { MM.addrOffset = MM.addrOffset addrVal .&. mask }


-- no side effects... yet
armPrimFnHasSideEffects :: ARMPrimFn f tp -> Bool
armPrimFnHasSideEffects = const False


rewritePrimFn :: ARMPrimFn (MC.Value ARM.AArch32 src) tp
              -> Rewriter ARM.AArch32 s src tgt (MC.Value ARM.AArch32 tgt tp)
rewritePrimFn f =
  case f of
    UDiv rep lhs rhs -> do
      tgtFn <- UDiv rep <$> rewriteValue lhs <*> rewriteValue rhs
      evalRewrittenArchFn tgtFn
    SDiv rep lhs rhs -> do
      tgtFn <- SDiv rep <$> rewriteValue lhs <*> rewriteValue rhs
      evalRewrittenArchFn tgtFn
    URem rep lhs rhs -> do
      tgtFn <- URem rep <$> rewriteValue lhs <*> rewriteValue rhs
      evalRewrittenArchFn tgtFn
    SRem rep lhs rhs -> do
      tgtFn <- SRem rep <$> rewriteValue lhs <*> rewriteValue rhs
      evalRewrittenArchFn tgtFn


-- ----------------------------------------------------------------------

-- FIXME: complete these instruction matchers when we know what we need for them

-- | Manually-provided semantics for A32 instructions whose full
-- semantics cannot be expressed in our semantics format.
--
-- This includes instructions with special side effects that we don't have a way
-- to talk about in the semantics; especially useful for architecture-specific
-- terminator statements.
a32InstructionMatcher :: ARMDis.Instruction -> Maybe (G.Generator ARM.AArch32 ids s ())
a32InstructionMatcher (ARMDis.Instruction opc operands) =
    case opc of
      ARMDis.SVC_A1 ->
        case operands of
          ARMDis.Bv4 _opPred ARMDis.:< ARMDis.Bv24 imm ARMDis.:< ARMDis.Nil -> Just $ do
            G.finishWithTerminator (MCB.ArchTermStmt (ARMSyscall imm))
      _ -> Nothing

-- | Manually-provided semantics for T32 (thumb) instructions whose full
-- semantics cannot be expressed in our semantics format.
--
-- This includes instructions with special side effects that we don't have a way
-- to talk about in the semantics; especially useful for architecture-specific
-- terminator statements.
t32InstructionMatcher :: ThumbDis.Instruction -> Maybe (G.Generator ARM.AArch32 ids s ())
t32InstructionMatcher (ThumbDis.Instruction opc _operands) =
    case opc of
      -- ThumbDis.TSVC -> case operands of
      --                    ThumbDis.Imm0_255 imm ThumbDis.:< ThumbDis.Nil ->
      --                        Just $ G.finishWithTerminator (MCB.ArchTermStmt (ThumbSyscall $ ThumbDis.Imm0_255 imm))
      -- ThumbDis.THINT -> case operands of
      --                     ThumbDis.Imm0_15 _imm ThumbDis.:< ThumbDis.Nil ->
      --                         Just $ return ()
      -- G.finishWithTerminator (MCB.ArchTermStmt (ThumbHint $ ThumbDis.Imm0_15 imm))
      _ -> Nothing
