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
import           Data.Macaw.ARM.ARMReg ()
import qualified Data.Macaw.Architecture.Info as MAI
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MCB
import           Data.Macaw.CFG.Rewriter ( Rewriter, rewriteValue, appendRewrittenArchStmt
                                         , evalRewrittenArchFn )
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.Types as MT
import           Data.Parameterized.Classes ( showF )
import qualified Data.Parameterized.List as PL
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
  -- | This is not great; it doesn't give us much ability to precisely reason
  -- about anything.  We'd have to havok every bit of state if we saw one.
  UninterpretedOpcode :: ARMDis.Opcode ARMDis.Operand sh
                      -> PL.List ARMDis.Operand sh
                      -> ARMStmt v

type instance MC.ArchStmt ARM.AArch32 = ARMStmt

instance MC.IsArchStmt ARMStmt where
    ppArchStmt _pp stmt =
        case stmt of
          UninterpretedOpcode opc ops -> PP.pretty (show opc) PP.<+> PP.pretty (FCls.toListFC showF ops)

instance TF.FunctorF ARMStmt where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ARMStmt where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ARMStmt where
  traverseF _go stmt =
    case stmt of
      UninterpretedOpcode opc ops -> pure (UninterpretedOpcode opc ops)

rewriteStmt :: ARMStmt (MC.Value ARM.AArch32 src) -> Rewriter ARM.AArch32 s src tgt ()
rewriteStmt s = appendRewrittenArchStmt =<< TF.traverseF rewriteValue s

-- | The ArchBlockPrecond type holds data required for an architecture to compute
-- new abstract states at the beginning on a block.
type instance MAI.ArchBlockPrecond ARM.AArch32 = ARMBlockPrecond

-- | In order to know how to decode a block, we need to know the value of
-- PSTATE_T (which is the Thumb/ARM mode) at the beginning of a block. We use
-- the 'MAI.ArchBlockPrecond' to communicate this between blocks (the core
-- discovery loop maintains it, and we compute the initial value when entering a
-- function).
data ARMBlockPrecond =
  ARMBlockPrecond { bpPSTATE_T :: Bool
                  }
  deriving (Eq, Ord, Show)


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

  UnsignedRSqrtEstimate :: (1 <= w)
                        => NR.NatRepr w
                        -> f (MT.BVType w)
                        -> ARMPrimFn f (MT.BVType w)

  FPSub :: (1 <= w)
        => NR.NatRepr w
        -> f (MT.BVType w)
        -> f (MT.BVType w)
        -> f (MT.BVType 32)
        -> ARMPrimFn f (MT.BVType w)
  FPAdd :: (1 <= w)
        => NR.NatRepr w
        -> f (MT.BVType w)
        -> f (MT.BVType w)
        -> f (MT.BVType 32)
        -> ARMPrimFn f (MT.BVType w)
  FPMul :: (1 <= w)
        => NR.NatRepr w
        -> f (MT.BVType w)
        -> f (MT.BVType w)
        -> f (MT.BVType 32)
        -> ARMPrimFn f (MT.BVType w)
  FPDiv :: (1 <= w)
        => NR.NatRepr w
        -> f (MT.BVType w)
        -> f (MT.BVType w)
        -> f (MT.BVType 32)
        -> ARMPrimFn f (MT.BVType w)

  FPRecipEstimate :: (1 <= w)
                  => NR.NatRepr w
                  -> f (MT.BVType w)
                  -> f (MT.BVType 32)
                  -> ARMPrimFn f (MT.BVType w)
  FPRecipStep :: (1 <= w)
              => NR.NatRepr w
              -> f (MT.BVType w)
              -> f (MT.BVType w)
              -> ARMPrimFn f (MT.BVType w)
  FPSqrtEstimate :: (1 <= w)
                 => NR.NatRepr w
                 -> f (MT.BVType w)
                 -> f (MT.BVType 32)
                 -> ARMPrimFn f (MT.BVType w)
  FPRSqrtStep :: (1 <= w)
              => NR.NatRepr w
              -> f (MT.BVType w)
              -> f (MT.BVType w)
              -> ARMPrimFn f (MT.BVType w)
  FPSqrt :: (1 <= w)
         => NR.NatRepr w
         -> f (MT.BVType w)
         -> f (MT.BVType 32)
         -> ARMPrimFn f (MT.BVType w)

  FPMax :: (1 <= w)
        => NR.NatRepr w
        -> f (MT.BVType w)
        -> f (MT.BVType w)
        -> f (MT.BVType 32)
        -> ARMPrimFn f (MT.BVType w)
  FPMin :: (1 <= w)
        => NR.NatRepr w
        -> f (MT.BVType w)
        -> f (MT.BVType w)
        -> f (MT.BVType 32)
        -> ARMPrimFn f (MT.BVType w)
  FPMaxNum :: (1 <= w)
           => NR.NatRepr w
           -> f (MT.BVType w)
           -> f (MT.BVType w)
           -> f (MT.BVType 32)
           -> ARMPrimFn f (MT.BVType w)
  FPMinNum :: (1 <= w)
           => NR.NatRepr w
           -> f (MT.BVType w)
           -> f (MT.BVType w)
           -> f (MT.BVType 32)
           -> ARMPrimFn f (MT.BVType w)

  FPMulAdd :: (1 <= w)
           => NR.NatRepr w
           -> f (MT.BVType w)
           -> f (MT.BVType w)
           -> f (MT.BVType w)
           -> f (MT.BVType 32)
           -> ARMPrimFn f (MT.BVType w)

  FPCompareGE :: (1 <= w)
              => NR.NatRepr w
              -> f (MT.BVType w)
              -> f (MT.BVType w)
              -> f (MT.BVType 32)
              -> ARMPrimFn f MT.BoolType
  FPCompareGT :: (1 <= w)
              => NR.NatRepr w
              -> f (MT.BVType w)
              -> f (MT.BVType w)
              -> f (MT.BVType 32)
              -> ARMPrimFn f MT.BoolType
  FPCompareEQ :: (1 <= w)
              => NR.NatRepr w
              -> f (MT.BVType w)
              -> f (MT.BVType w)
              -> f (MT.BVType 32)
              -> ARMPrimFn f MT.BoolType
  FPCompareNE :: (1 <= w)
              => NR.NatRepr w
              -> f (MT.BVType w)
              -> f (MT.BVType w)
              -> f (MT.BVType 32)
              -> ARMPrimFn f MT.BoolType
  FPCompareUN :: (1 <= w)
              => NR.NatRepr w
              -> f (MT.BVType w)
              -> f (MT.BVType w)
              -> f (MT.BVType 32)
              -> ARMPrimFn f MT.BoolType

  FPToFixed :: (1 <= w, 1 <= x)
            => NR.NatRepr w
            -> f (MT.BVType x)
            -> f (MT.BVType 32)
            -> f MT.BoolType
            -> f (MT.BVType 32)
            -> f (MT.BVType 3)
            -> ARMPrimFn f (MT.BVType w)
  FixedToFP :: (1 <= w, 1 <= x)
            => NR.NatRepr w
            -> f (MT.BVType x)
            -> f (MT.BVType 32)
            -> f MT.BoolType
            -> f (MT.BVType 32)
            -> f (MT.BVType 3)
            -> ARMPrimFn f (MT.BVType w)
  FPConvert :: (1 <= w, 1 <= x)
            => NR.NatRepr w
            -> f (MT.BVType x)
            -> f (MT.BVType 32)
            -> f (MT.BVType 3)
            -> ARMPrimFn f (MT.BVType w)
  FPToFixedJS :: f (MT.BVType 64)
              -> f (MT.BVType 32)
              -> f MT.BoolType
              -> ARMPrimFn f (MT.BVType 32)
  FPRoundInt :: (1 <= w)
             => NR.NatRepr w
             -> f (MT.BVType w)
             -> f (MT.BVType 32)
             -> f (MT.BVType 3)
             -> f MT.BoolType
             -> ARMPrimFn f (MT.BVType w)

instance MC.IsArchFn ARMPrimFn where
    ppArchFn pp f =
        let ppUnary s v' = PP.text s PP.<+> v'
            ppBinary s v1' v2' = PP.text s PP.<+> v1' PP.<+> v2'
            ppTernary s v1' v2' v3' = PP.text s PP.<+> v1' PP.<+> v2' PP.<+> v3'
        in case f of
          UDiv _ lhs rhs -> ppBinary "arm_udiv" <$> pp lhs <*> pp rhs
          SDiv _ lhs rhs -> ppBinary "arm_sdiv" <$> pp lhs <*> pp rhs
          URem _ lhs rhs -> ppBinary "arm_urem" <$> pp lhs <*> pp rhs
          SRem _ lhs rhs -> ppBinary "arm_srem" <$> pp lhs <*> pp rhs
          UnsignedRSqrtEstimate _ v -> ppUnary "arm_unsignedRSqrtEstimate" <$> pp v
          FPSub _ lhs rhs _fpscr -> ppBinary "arm_fpsub" <$> pp lhs <*> pp rhs
          FPAdd _ lhs rhs _fpscr -> ppBinary "arm_fpadd" <$> pp lhs <*> pp rhs
          FPMul _ lhs rhs _fpscr -> ppBinary "arm_fpmul" <$> pp lhs <*> pp rhs
          FPDiv _ lhs rhs _fpscr -> ppBinary "arm_fpdiv" <$> pp lhs <*> pp rhs
          FPRecipEstimate _ v _fpscr -> ppUnary "arm_fpRecipEstimate" <$> pp v
          FPRecipStep _ v _fpscr -> ppUnary "arm_fpRecipStep" <$> pp v
          FPSqrtEstimate _ v _fpscr -> ppUnary "arm_fpSqrtEstimate" <$> pp v
          FPRSqrtStep _ v _fpscr -> ppUnary "arm_fpRSqrtStep" <$> pp v
          FPSqrt _ v _fpscr -> ppUnary "arm_fpSqrt" <$> pp v
          FPMax _ lhs rhs _fpscr -> ppBinary "arm_fpMax" <$> pp lhs <*> pp rhs
          FPMin _ lhs rhs _fpscr -> ppBinary "arm_fpMin" <$> pp lhs <*> pp rhs
          FPMaxNum _ lhs rhs _fpscr -> ppBinary "arm_fpMaxNum" <$> pp lhs <*> pp rhs
          FPMinNum _ lhs rhs _fpscr -> ppBinary "arm_fpMinNum" <$> pp lhs <*> pp rhs
          FPMulAdd _ o1 o2 o3 _fpscr -> ppTernary "arm_fpMulAdd" <$> pp o1 <*> pp o2 <*> pp o3
          FPCompareGE _ lhs rhs _fpscr -> ppBinary "arm_fpCompareGE" <$> pp lhs <*> pp rhs
          FPCompareGT _ lhs rhs _fpscr -> ppBinary "arm_fpCompareGT" <$> pp lhs <*> pp rhs
          FPCompareEQ _ lhs rhs _fpscr -> ppBinary "arm_fpCompareEQ" <$> pp lhs <*> pp rhs
          FPCompareNE _ lhs rhs _fpscr -> ppBinary "arm_fpCompareNE" <$> pp lhs <*> pp rhs
          FPCompareUN _ lhs rhs _fpscr -> ppBinary "arm_fpCompareUN" <$> pp lhs <*> pp rhs
          FPToFixed _ v _ b _ fl -> ppTernary "arm_fpToFixed" <$> pp v <*> pp b <*> pp fl
          FixedToFP _ v _ b _ fl -> ppTernary "arm_fixedToFP" <$> pp v <*> pp b <*> pp fl
          FPConvert _ v _fpscr fl -> ppBinary "arm_fpConvert" <$> pp v <*> pp fl
          FPToFixedJS v _ b -> ppBinary "arm_fpToFixedJS" <$> pp v <*> pp b
          FPRoundInt _ v _ fl b -> ppTernary "arm_fpRoundInt" <$> pp v <*> pp fl <*> pp b

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
      UnsignedRSqrtEstimate rep v -> UnsignedRSqrtEstimate rep <$> go v
      FPSub rep lhs rhs fpscr -> FPSub rep <$> go lhs <*> go rhs <*> go fpscr
      FPAdd rep lhs rhs fpscr -> FPAdd rep <$> go lhs <*> go rhs <*> go fpscr
      FPMul rep lhs rhs fpscr -> FPMul rep <$> go lhs <*> go rhs <*> go fpscr
      FPDiv rep lhs rhs fpscr -> FPDiv rep <$> go lhs <*> go rhs <*> go fpscr
      FPRecipEstimate rep v fpscr -> FPRecipEstimate rep <$> go v <*> go fpscr
      FPRecipStep rep v fpscr -> FPRecipStep rep <$> go v <*> go fpscr
      FPSqrtEstimate rep v fpscr -> FPSqrtEstimate rep <$> go v <*> go fpscr
      FPRSqrtStep rep v fpscr -> FPRSqrtStep rep <$> go v <*> go fpscr
      FPSqrt rep v fpscr -> FPSqrt rep <$> go v <*> go fpscr
      FPMax rep lhs rhs fpscr -> FPMax rep <$> go lhs <*> go rhs <*> go fpscr
      FPMin rep lhs rhs fpscr -> FPMin rep <$> go lhs <*> go rhs <*> go fpscr
      FPMaxNum rep lhs rhs fpscr -> FPMaxNum rep <$> go lhs <*> go rhs <*> go fpscr
      FPMinNum rep lhs rhs fpscr -> FPMinNum rep <$> go lhs <*> go rhs <*> go fpscr
      FPMulAdd rep a b c fpscr -> FPMulAdd rep <$> go a <*> go b <*> go c <*> go fpscr
      FPCompareGE rep lhs rhs fpscr -> FPCompareGE rep <$> go lhs <*> go rhs <*> go fpscr
      FPCompareGT rep lhs rhs fpscr -> FPCompareGT rep <$> go lhs <*> go rhs <*> go fpscr
      FPCompareEQ rep lhs rhs fpscr -> FPCompareEQ rep <$> go lhs <*> go rhs <*> go fpscr
      FPCompareNE rep lhs rhs fpscr -> FPCompareNE rep <$> go lhs <*> go rhs <*> go fpscr
      FPCompareUN rep lhs rhs fpscr -> FPCompareUN rep <$> go lhs <*> go rhs <*> go fpscr
      FPToFixed rep a b c d e -> FPToFixed rep <$> go a <*> go b <*> go c <*> go d <*> go e
      FixedToFP rep a b c d e -> FixedToFP rep <$> go a <*> go b <*> go c <*> go d <*> go e
      FPConvert rep a b c -> FPConvert rep <$> go a <*> go b <*> go c
      FPToFixedJS a b c -> FPToFixedJS <$> go a <*> go b <*> go c
      FPRoundInt rep a b c d -> FPRoundInt rep <$> go a <*> go b <*> go c <*> go d


type instance MC.ArchFn ARM.AArch32 = ARMPrimFn

instance MT.HasRepr (ARMPrimFn (MC.Value ARM.AArch32 ids)) MT.TypeRepr where
  typeRepr f =
    case f of
      UDiv rep _ _ -> MT.BVTypeRepr rep
      SDiv rep _ _ -> MT.BVTypeRepr rep
      URem rep _ _ -> MT.BVTypeRepr rep
      SRem rep _ _ -> MT.BVTypeRepr rep
      UnsignedRSqrtEstimate rep _ -> MT.BVTypeRepr rep
      FPSub rep _ _ _ -> MT.BVTypeRepr rep
      FPAdd rep _ _ _ -> MT.BVTypeRepr rep
      FPMul rep _ _ _ -> MT.BVTypeRepr rep
      FPDiv rep _ _ _ -> MT.BVTypeRepr rep
      FPRecipEstimate rep _ _ -> MT.BVTypeRepr rep
      FPRecipStep rep _ _ -> MT.BVTypeRepr rep
      FPSqrtEstimate rep _ _ -> MT.BVTypeRepr rep
      FPRSqrtStep rep _ _ -> MT.BVTypeRepr rep
      FPSqrt rep _ _ -> MT.BVTypeRepr rep
      FPMax rep _ _ _ -> MT.BVTypeRepr rep
      FPMin rep _ _ _ -> MT.BVTypeRepr rep
      FPMaxNum rep _ _ _ -> MT.BVTypeRepr rep
      FPMinNum rep _ _ _ -> MT.BVTypeRepr rep
      FPMulAdd rep _ _ _ _ -> MT.BVTypeRepr rep
      FPCompareGE {} -> MT.BoolTypeRepr
      FPCompareGT {} -> MT.BoolTypeRepr
      FPCompareEQ {} -> MT.BoolTypeRepr
      FPCompareNE {} -> MT.BoolTypeRepr
      FPCompareUN {} -> MT.BoolTypeRepr
      FPToFixed rep _ _ _ _ _ -> MT.BVTypeRepr rep
      FixedToFP rep _ _ _ _ _ -> MT.BVTypeRepr rep
      FPConvert rep _ _ _ -> MT.BVTypeRepr rep
      FPToFixedJS {} -> MT.BVTypeRepr (NR.knownNat @32)
      FPRoundInt rep _ _ _ _ -> MT.BVTypeRepr rep



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
    UnsignedRSqrtEstimate rep v ->
      evalRewrittenArchFn =<< (UnsignedRSqrtEstimate rep <$> rewriteValue v)
    FPSub rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPSub rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPAdd rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPAdd rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPMul rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPMul rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPDiv rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPDiv rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPRecipEstimate rep v fpscr ->
      evalRewrittenArchFn =<< (FPRecipEstimate rep <$> rewriteValue v <*> rewriteValue fpscr)
    FPRecipStep rep v fpscr ->
      evalRewrittenArchFn =<< (FPRecipStep rep <$> rewriteValue v <*> rewriteValue fpscr)
    FPSqrtEstimate rep v fpscr ->
      evalRewrittenArchFn =<< (FPSqrtEstimate rep <$> rewriteValue v <*> rewriteValue fpscr)
    FPRSqrtStep rep v fpscr ->
      evalRewrittenArchFn =<< (FPRSqrtStep rep <$> rewriteValue v <*> rewriteValue fpscr)
    FPSqrt rep v fpscr ->
      evalRewrittenArchFn =<< (FPSqrt rep <$> rewriteValue v <*> rewriteValue fpscr)
    FPMax rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPMax rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPMin rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPMin rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPMaxNum rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPMaxNum rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPMinNum rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPMinNum rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPMulAdd rep a b c fpscr ->
      evalRewrittenArchFn =<< (FPMulAdd rep <$> rewriteValue a <*> rewriteValue b <*> rewriteValue c <*> rewriteValue fpscr)
    FPCompareGE rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPCompareGE rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPCompareGT rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPCompareGT rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPCompareEQ rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPCompareEQ rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPCompareNE rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPCompareNE rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPCompareUN rep lhs rhs fpscr ->
      evalRewrittenArchFn =<< (FPCompareUN rep <$> rewriteValue lhs <*> rewriteValue rhs <*> rewriteValue fpscr)
    FPToFixed rep a b c d e ->
      evalRewrittenArchFn =<< (FPToFixed rep <$> rewriteValue a <*> rewriteValue b <*> rewriteValue c <*> rewriteValue d <*> rewriteValue e)
    FixedToFP rep a b c d e ->
      evalRewrittenArchFn =<< (FixedToFP rep <$> rewriteValue a <*> rewriteValue b <*> rewriteValue c <*> rewriteValue d <*> rewriteValue e)
    FPConvert rep a b c ->
      evalRewrittenArchFn =<< (FPConvert rep <$> rewriteValue a <*> rewriteValue b <*> rewriteValue c)
    FPToFixedJS a b c ->
      evalRewrittenArchFn =<< (FPToFixedJS <$> rewriteValue a <*> rewriteValue b <*> rewriteValue c)
    FPRoundInt rep a b c d ->
      evalRewrittenArchFn =<< (FPRoundInt rep <$> rewriteValue a <*> rewriteValue b <*> rewriteValue c <*> rewriteValue d)

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
      _ | isUninterpretedOpcode opc -> Just $ do
            G.addStmt (MC.ExecArchStmt (UninterpretedOpcode opc operands))
        | otherwise -> Nothing

-- | This is a coarse heuristic to treat any instruction beginning with 'V' as a
-- vector instruction that we want to leave uninterpreted, as translating all of
-- the vector instructions faithfully is too much code (for now)
isUninterpretedOpcode :: (Show a) => a -> Bool
isUninterpretedOpcode opc =
  case show opc of
    'V':_ -> True
    _ -> False

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
