{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
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
module Data.Macaw.ARM.Arch
    -- ( ARMArchConstraints
    -- , ARMStmt(..)
    -- , armPrimFnHasSideEffects
    -- )
    where

import           Data.Bits ( (.&.) )
import           Data.Macaw.ARM.ARMReg
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MCB
import           Data.Macaw.CFG.Rewriter ( Rewriter, rewriteValue, appendRewrittenArchStmt
                                         , evalRewrittenArchFn )
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FCls
import qualified Dismantle.ARM as ARMDis
import qualified Dismantle.ARM.Operands as ARMOperands
import qualified Dismantle.Thumb as ThumbDis
import           GHC.TypeLits
import qualified SemMC.Architecture.AArch32 as ARM
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Text.PrettyPrint.HughesPJClass as HPP

-- ----------------------------------------------------------------------
-- ARM-specific statement definitions

data ARMStmt (v :: MT.Type -> *) where
    WhatShouldThisBe :: ARMStmt v

type instance MC.ArchStmt ARM.AArch32 = ARMStmt

instance MC.IsArchStmt ARMStmt where
    ppArchStmt _pp stmt =
        case stmt of
          WhatShouldThisBe -> PP.text "arm_what?"

instance TF.FunctorF ARMStmt where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ARMStmt where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ARMStmt where
  traverseF _go stmt =
    case stmt of
      WhatShouldThisBe -> pure WhatShouldThisBe

rewriteStmt :: (MC.ArchStmt arm ~ ARMStmt) =>
               ARMStmt (MC.Value arm src) -> Rewriter arm s src tgt ()
rewriteStmt s = appendRewrittenArchStmt =<< TF.traverseF rewriteValue s


-- ----------------------------------------------------------------------
-- ARM terminal statements (which have instruction-specific effects on
-- control-flow and register state).

data ARMTermStmt ids where
    ARMSyscall :: ARMOperands.SvcOperand -> ARMTermStmt ids
    ThumbSyscall :: ThumbDis.Operand "Imm0_255" -> ARMTermStmt ids

deriving instance Show (ARMTermStmt ids)

type instance MC.ArchTermStmt ARM.AArch32 = ARMTermStmt

instance MC.PrettyF ARMTermStmt where
    prettyF ts = let dpp2app :: forall a. HPP.Pretty a => a -> PP.Doc
                     dpp2app = PP.text . show . HPP.pPrint
                     -- ugh: dismantle uses HPP, Arch uses PP.
                 in case ts of
                      ARMSyscall v -> PP.text "arm_syscall" PP.<+> dpp2app v
                      ThumbSyscall (ThumbDis.Imm0_255 v) ->
                          -- dpp2app $ ThumbDis.ppInstruction ts
                          PP.text "thumb_syscall" PP.<+>
                          (PP.text $ show v)
                          --               (PP.text $ ThumbDis.operandReprString v)


-- instance PrettyF (ArchTermStmt ARM.AArch32))

rewriteTermStmt :: ARMTermStmt src -> Rewriter arm s src tgt (ARMTermStmt tgt)
rewriteTermStmt s =
    case s of
      ARMSyscall v -> pure $ ARMSyscall v
      ThumbSyscall v -> pure $ ThumbSyscall v


-- ----------------------------------------------------------------------
-- ARM functions.  These may return a value, and may depend on the
-- current state of the heap and the set of registeres defined so far
-- and the result type, but should not affect the processor state.

-- type family ArchStmt (arch :: *) :: (Type -> *) -> *
-- data ARMStmt (v :: MT.Type -> *) where
--     WhatShouldThisBe :: ARMStmt v
-- type instance MC.ArchStmt ARM.AArch32 = ARMStmt

-- type family ArchFn :: (arch :: *) :: (Type -> *) -> Type -> *
-- data ARMPrimFn f (tp :: (MT.Type -> *) -> MT.Type) where
--     NoPrimKnown :: ARMPrimFn tp

data ARMPrimFn arm f tp where
    -- | Unsigned division remainder
    --
    -- Division by zero does not have side effects, but instead produces an undefined value
    URem :: NR.NatRepr (MC.RegAddrWidth (MC.ArchReg arm))
         -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
         -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
         -> ARMPrimFn arm f (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))

instance MC.IsArchFn (ARMPrimFn arm) where
    ppArchFn pp f =
        let ppBinary s v1' v2' = PP.text s PP.<+> v1' PP.<+> v2'
        in case f of
          URem _w dividend divisor -> ppBinary "arm_urem" <$> pp dividend <*> pp divisor

instance FCls.FunctorFC (ARMPrimFn arm) where
  fmapFC = FCls.fmapFCDefault

instance FCls.FoldableFC (ARMPrimFn arm) where
  foldMapFC = FCls.foldMapFCDefault

instance FCls.TraversableFC (ARMPrimFn arm) where
  traverseFC go f =
    case f of
      URem w dividend divisor -> URem w <$> go dividend <*> go divisor

type instance MC.ArchFn ARM.AArch32 = ARMPrimFn ARM.AArch32

instance (1 <= MC.RegAddrWidth (MC.ArchReg arm)) => MT.HasRepr (ARMPrimFn arm (MC.Value arm ids)) MT.TypeRepr where
  typeRepr f =
    case f of
      URem rep _ _ -> MT.BVTypeRepr rep


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
armPrimFnHasSideEffects :: ARMPrimFn arm f tp -> Bool
armPrimFnHasSideEffects = const False


rewritePrimFn :: (ARMArchConstraints arm, MC.ArchFn arm ~ ARMPrimFn arm)
              => ARMPrimFn arm (MC.Value arm src) tp
              -> Rewriter arm s src tgt (MC.Value arm tgt tp)
rewritePrimFn f =
  case f of
    URem w dividend divisor -> do
      tgtFn <- URem w <$> rewriteValue dividend <*> rewriteValue divisor
      evalRewrittenArchFn tgtFn


-- ----------------------------------------------------------------------
-- The aggregate set of architectural constraints to express for ARM
-- computations

type ARMArchConstraints arm = ( MC.ArchReg arm ~ ARMReg
                              , MC.ArchFn arm ~ ARMPrimFn arm
                              , MC.ArchStmt arm ~ ARMStmt
                              , MC.ArchTermStmt arm ~ ARMTermStmt
                              , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg arm))
                              , 1 <= MC.RegAddrWidth ARMReg
                              , KnownNat (MC.RegAddrWidth ARMReg)
                              , MC.ArchConstraints arm
                              , O.ExtractValue arm ARMOperands.GPR (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
                              , O.ExtractValue arm (Maybe ARMOperands.GPR) (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
                              )


-- ----------------------------------------------------------------------

-- | Manually-provided semantics for A32 instructions whose full
-- semantics cannot be expressed in our semantics format.
--
-- This includes instructions with special side effects that we don't have a way
-- to talk about in the semantics; especially useful for architecture-specific
-- terminator statements.
a32InstructionMatcher :: (ARMArchConstraints arch) =>
                         ARMDis.Instruction -> Maybe (G.Generator arch ids s ())
a32InstructionMatcher (ARMDis.Instruction opc operands) =
    case opc of
      ARMDis.SVC -> case operands of
                      ARMDis.Pred _opPred ARMDis.:< ARMDis.Imm24b imm ARMDis.:< ARMDis.Nil ->
                          Just $ G.finishWithTerminator (MCB.ArchTermStmt (ARMSyscall imm))
      _ -> Nothing

-- | Manually-provided semantics for T32 (thumb) instructions whose full
-- semantics cannot be expressed in our semantics format.
--
-- This includes instructions with special side effects that we don't have a way
-- to talk about in the semantics; especially useful for architecture-specific
-- terminator statements.
t32InstructionMatcher :: (ARMArchConstraints arch) =>
                         ThumbDis.Instruction -> Maybe (G.Generator arch ids s ())
t32InstructionMatcher (ThumbDis.Instruction opc operands) =
    case opc of
      ThumbDis.TSVC -> case operands of
                         ThumbDis.Imm0_255 imm ThumbDis.:< ThumbDis.Nil ->
                             Just $ G.finishWithTerminator (MCB.ArchTermStmt (ThumbSyscall $ ThumbDis.Imm0_255 imm))
      ThumbDis.THINT -> case operands of
                          ThumbDis.Imm0_15 _imm ThumbDis.:< ThumbDis.Nil ->
                              Just $ return ()
                                   -- G.finishWithTerminator (MCB.ArchTermStmt (ThumbHint $ ThumbDis.Imm0_15 imm))
      _ -> Nothing
