{-# LANGUAGE BinaryLiterals #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE OverloadedStrings #-}
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

import           Control.Applicative ( (<|>) )
import           Data.Bits ( (.&.) )
import           Data.Kind ( Type )
import qualified Data.Macaw.ARM.ARMReg as ARMReg
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MCB
import           Data.Macaw.CFG.Rewriter ( Rewriter, rewriteValue, appendRewrittenArchStmt
                                         , evalRewrittenArchFn )
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Simplify as MSS
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.Classes as PC
import qualified Data.Parameterized.List as PL
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FCls
import qualified Data.Word.Indexed as WI
import qualified Dismantle.ARM.A32 as ARMDis
import qualified Dismantle.ARM.T32 as ThumbDis
import           GHC.TypeLits
import qualified Language.ASL.Globals as ASL
import qualified Prettyprinter as PP
import qualified SemMC.Architecture.AArch32 as ARM

-- ----------------------------------------------------------------------
-- ARM-specific statement definitions

data ARMStmt (v :: MT.Type -> Type) where
  -- | This is not great; it doesn't give us much ability to precisely reason
  -- about anything.  We'd have to havok every bit of state if we saw one.
  UninterpretedA32Opcode :: ARMDis.Opcode ARMDis.Operand sh
                         -> PL.List ARMDis.Operand sh
                         -> ARMStmt v
  UninterpretedT32Opcode :: ThumbDis.Opcode ThumbDis.Operand sh
                         -> PL.List ThumbDis.Operand sh
                         -> ARMStmt v

type instance MC.ArchStmt ARM.AArch32 = ARMStmt

instance MC.IsArchStmt ARMStmt where
    ppArchStmt _pp stmt =
        case stmt of
          UninterpretedA32Opcode opc ops -> PP.viaShow opc PP.<+> PP.pretty (FCls.toListFC PC.showF ops)
          UninterpretedT32Opcode opc ops -> PP.viaShow opc PP.<+> PP.pretty (FCls.toListFC PC.showF ops)

instance TF.FunctorF ARMStmt where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ARMStmt where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ARMStmt where
  traverseF _go stmt =
    case stmt of
      UninterpretedA32Opcode opc ops -> pure (UninterpretedA32Opcode opc ops)
      UninterpretedT32Opcode opc ops -> pure (UninterpretedT32Opcode opc ops)

rewriteStmt :: ARMStmt (MC.Value ARM.AArch32 src) -> Rewriter ARM.AArch32 s src tgt ()
rewriteStmt s = appendRewrittenArchStmt =<< TF.traverseF rewriteValue s

-- | The ArchBlockPrecond type holds data required for an architecture to compute
-- new abstract states at the beginning on a block.
type instance MC.ArchBlockPrecond ARM.AArch32 = ARMBlockPrecond

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

data ARMTermStmt f where
  -- | Return if the condition is true; otherwise, fall through to the next instruction
  ReturnIf :: f MT.BoolType -> ARMTermStmt f
  -- | Return if the condition is not true; otherwise, fall through to the next instruction
  --
  -- Note that it is unfortunate that we need this in addition to 'ReturnIf'. At
  -- the part of the analysis where we are able to generate these block
  -- terminators, we cannot generate new statements since we do not have the
  -- right nonce generator. As a result, if we are returning when the condition
  -- is false, we are not able to generate a negation (which would require
  -- wrapping the original condition in an Assignment, which has an AssignId,
  -- which requires a nonce). We work around this by just having an additional
  -- block terminator.
  ReturnIfNot :: f MT.BoolType -> ARMTermStmt f

instance Show (ARMTermStmt (MC.Value ARM.AArch32 ids)) where
  show ts = show (MC.ppArchTermStmt PP.pretty ts)

type instance MC.ArchTermStmt ARM.AArch32 = ARMTermStmt

instance MC.IsArchTermStmt ARMTermStmt where
  ppArchTermStmt ppValue ts =
    case ts of
      ReturnIf cond -> "return_if" PP.<+> ppValue cond
      ReturnIfNot cond -> "return_if_not" PP.<+> ppValue cond

instance TF.FoldableF ARMTermStmt where
  foldMapF = TF.foldMapFDefault

instance TF.FunctorF ARMTermStmt where
  fmapF = TF.fmapFDefault

instance TF.TraversableF ARMTermStmt where
  traverseF go tstmt =
    case tstmt of
      ReturnIf cond -> ReturnIf <$> go cond
      ReturnIfNot cond -> ReturnIfNot <$> go cond

rewriteTermStmt :: ARMTermStmt (MC.Value ARM.AArch32 src) -> Rewriter ARM.AArch32 s src tgt (ARMTermStmt (MC.Value ARM.AArch32 tgt))
rewriteTermStmt s =
    case s of
      ReturnIf cond -> ReturnIf <$> rewriteValue cond
      ReturnIfNot cond -> ReturnIfNot <$> rewriteValue cond

-- ----------------------------------------------------------------------
-- ARM functions.  These may return a value, and may depend on the
-- current state of the heap and the set of registers defined so far
-- and the result type, but should not affect the processor state.

zeroExtend :: (KnownNat n2, n1 <= n2) => WI.W n1 -> NR.NatRepr n2 -> WI.W n2
zeroExtend w _rep = WI.w (WI.unW w)

data ARMPrimFn (f :: MT.Type -> Type) tp where
  -- | Issue a system call
  --
  -- The intent is that the user provides a mapping from system call numbers to
  -- handlers in macaw-aarch32-symbolic, enabling the translation to crucible to
  -- replace this operation with a lookup + call to a function handle.  By
  -- capturing all of the necessary registers as inputs and outputs here,
  -- uniform treatment is possible.  See the x86 version for a more detailed
  -- account of the translation strategy.
  --
  -- The 'WI.W' is the immediate operand embedded in the opcode
  --
  -- The rest of the arguments are all of the registers that participate in the
  -- syscall protocol (at least on Linux). Arguments are passed in r0-r6, while
  -- the syscall number is in r7.
  --
  -- The system call can return up to two values (in r0 and r1)
  ARMSyscall :: WI.W 24
             -> f (MT.BVType 32) -- r0
             -> f (MT.BVType 32) -- r1
             -> f (MT.BVType 32) -- r2
             -> f (MT.BVType 32) -- r3
             -> f (MT.BVType 32) -- r4
             -> f (MT.BVType 32) -- r5
             -> f (MT.BVType 32) -- r6
             -> f (MT.BVType 32) -- r7 (syscall number)
             -> ARMPrimFn f (MT.TupleType [MT.BVType 32, MT.BVType 32])

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

  UnsignedRSqrtEstimate :: (KnownNat w, 1 <= w)
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
        let ppUnary s v' = s PP.<+> v'
            ppBinary s v1' v2' = s PP.<+> v1' PP.<+> v2'
            ppTernary s v1' v2' v3' = s PP.<+> v1' PP.<+> v2' PP.<+> v3'
            ppSC s imm r0 r1 r2 r3 r4 r5 r6 r7 = s PP.<+> PP.viaShow imm PP.<+> r0 PP.<+> r1 PP.<+> r2 PP.<+> r3 PP.<+> r4 PP.<+> r5 PP.<+> r6 PP.<+> r7
        in case f of
          ARMSyscall imm r0 r1 r2 r3 r4 r5 r6 r7 ->
            ppSC "arm_syscall" imm <$> pp r0 <*> pp r1 <*> pp r2 <*> pp r3 <*> pp r4 <*> pp r5 <*> pp r6 <*> pp r7
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
      ARMSyscall imm r0 r1 r2 r3 r4 r5 r6 r7 ->
        ARMSyscall imm <$> go r0 <*> go r1 <*> go r2 <*> go r3 <*> go r4 <*> go r5 <*> go r6 <*> go r7
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

instance MT.HasRepr (ARMPrimFn f) MT.TypeRepr where
  typeRepr f =
    case f of
      ARMSyscall {} -> PC.knownRepr
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
    ARMSyscall imm r0 r1 r2 r3 r4 r5 r6 r7 -> do
      tgtFn <- ARMSyscall imm <$> rewriteValue r0 <*> rewriteValue r1 <*> rewriteValue r2 <*> rewriteValue r3 <*> rewriteValue r4 <*> rewriteValue r5 <*> rewriteValue r6 <*> rewriteValue r7
      evalRewrittenArchFn tgtFn
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

evalAssignRhs :: MC.AssignRhs ARM.AArch32 (MC.Value ARM.AArch32 ids) tp
              -> G.Generator ARM.AArch32 ids s (G.Expr ARM.AArch32 ids tp)
evalAssignRhs rhs =
  G.ValueExpr . MC.AssignedValue <$> G.addAssignment rhs

-- | Evaluate an architecture-specific function and return the resulting expr.
evalArchFn :: ARMPrimFn (MC.Value ARM.AArch32 ids) tp
           -> G.Generator ARM.AArch32 ids s (G.Expr ARM.AArch32 ids tp)
evalArchFn f = evalAssignRhs (MC.EvalArchFn f (MT.typeRepr f))

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
            let r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
            let r1 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")
            sc <- ARMSyscall imm <$> G.getRegVal r0
                                 <*> G.getRegVal r1
                                 <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2"))
                                 <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3"))
                                 <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R4"))
                                 <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R5"))
                                 <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R6"))
                                 <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R7"))
            res <- G.addExpr =<< evalArchFn sc
            G.setRegVal r0 =<< G.addExpr (G.AppExpr (MC.TupleField PC.knownRepr res PL.index0))
            G.setRegVal r1 =<< G.addExpr (G.AppExpr (MC.TupleField PC.knownRepr res PL.index1))

            -- Increment the PC; we don't get the normal PC increment from the
            -- ASL semantics, since we are intercepting them to just add this statement
            let pc = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_PC")
            pc_orig <- G.getRegVal pc
            pc_next <- G.addExpr (G.AppExpr (MC.BVAdd NR.knownNat pc_orig (MC.BVValue NR.knownNat 4)))
            G.setRegVal pc pc_next

            G.finishWithTerminator MCB.FetchAndExecute
      _ | isUninterpretedOpcode opc -> Just $ do
            G.addStmt (MC.ExecArchStmt (UninterpretedA32Opcode opc operands))
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
t32InstructionMatcher (ThumbDis.Instruction opc operands) =
    case opc of
      ThumbDis.SVC_T1 ->
        case operands of
          ThumbDis.Bv8 imm8 ThumbDis.:< ThumbDis.Nil -> Just $ do
            let r0 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R0")
            let r1 = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R1")

            -- Thumb uses an 8 bit immediate instead of the 24 used in ARM
            -- syscalls. The kernel can't tell the difference between which
            -- instruction was used to enter a syscall (it *could* but doesn't),
            -- so we can just zero extend the immediate value and use the same
            -- syscall representation in macaw
            let imm24 = zeroExtend imm8 (NR.knownNat @24)
            sc <- ARMSyscall imm24 <$> G.getRegVal r0
                                   <*> G.getRegVal r1
                                   <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R2"))
                                   <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R3"))
                                   <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R4"))
                                   <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R5"))
                                   <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R6"))
                                   <*> G.getRegVal (ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_R7"))
            res <- G.addExpr =<< evalArchFn sc
            G.setRegVal r0 =<< G.addExpr (G.AppExpr (MC.TupleField PC.knownRepr res PL.index0))
            G.setRegVal r1 =<< G.addExpr (G.AppExpr (MC.TupleField PC.knownRepr res PL.index1))

            -- Increment the PC; we don't get the normal PC increment from the
            -- ASL semantics, since we are intercepting them to just add this statement
            let pc = ARMReg.ARMGlobalBV (ASL.knownGlobalRef @"_PC")
            pc_orig <- G.getRegVal pc
            pc_next <- G.addExpr (G.AppExpr (MC.BVAdd NR.knownNat pc_orig (MC.BVValue NR.knownNat 2)))
            G.setRegVal pc pc_next

            G.finishWithTerminator MCB.FetchAndExecute

      _ | isUninterpretedOpcode opc -> Just $ do
            G.addStmt (MC.ExecArchStmt (UninterpretedT32Opcode opc operands))
        | otherwise -> Nothing

instance MSS.SimplifierExtension ARM.AArch32 where
  simplifyArchApp = saturatingSimplify
  simplifyArchFn = armSimplifyArchFn

armSimplifyArchFn :: MC.ArchFn ARM.AArch32 (MC.Value ARM.AArch32 ids) tp
                  -> MT.TypeRepr tp
                  -> Maybe (MC.Value ARM.AArch32 ids tp)
armSimplifyArchFn af _rep =
  case af of
    SRem _ z@(MC.BVValue _ 0) _ -> return z
    URem _ z@(MC.BVValue _ 0) _ -> return z
    SDiv _ z@(MC.BVValue _ 0) _ -> return z
    UDiv _ z@(MC.BVValue _ 0) _ -> return z
    _ -> Nothing

simplifyOnce :: MC.App (MC.Value ARM.AArch32 ids) tp
             -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyOnce a = simplifyTruncExt a
              <|> simplifyTrivialTruncExt a
              <|> coalesceAdditionByConstant a
              <|> simplifyNestedMux a
              <|> distributeAddOverConstantMux a
              <|> doubleNegation a
              <|> negatedTrivialMux a
              <|> negatedMux a

-- | Apply the simplification rules until nothing changes
--
-- Simplifications can trigger other simplifications, and there is no fixed
-- order in which we can guarantee that everything will fire correctly.  Thus,
-- we apply rules until we saturate them.
saturatingSimplify :: MC.App (MC.Value ARM.AArch32 ids) tp
                   -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
saturatingSimplify a0 =
  case simplifyOnce a0 of
    Nothing -> Nothing
    Just a1 -> simplifyMany a1
  where
    simplifyMany a1 =
      case simplifyOnce a1 of
        Nothing -> Just a1
        Just a2 -> simplifyMany a2

-- | Simplify terms that extend a pointer, increment it, and then truncate it
-- back to 32 bits.
--
-- These sequences interfere with the abstract interpretation of especially the
-- stack pointer, which just sends any ext/trunc operations to Top.
--
-- > r1 := (uext val 65)
-- > r2 := (bv_add r1 (constant :: [65]))
-- > r3 := (trunc r2 32)
--
-- to (bv_add val (constant :: [32]))
simplifyTruncExt :: MC.App (MC.Value ARM.AArch32 ids) tp
                 -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyTruncExt r3 = do
  MC.Trunc r2 rep3 <- return r3
  let targetSize = NR.knownNat @32
  PC.Refl <- PC.testEquality rep3 targetSize
  MC.AssignedValue (MC.Assignment _r2_id (MC.EvalApp (MC.BVAdd _rep2 r1 constant))) <- return r2
  MC.BVValue constantRepr constantVal <- return constant
  PC.Refl <- PC.testEquality constantRepr (NR.knownNat @65)
  MC.AssignedValue (MC.Assignment _r1_id (MC.EvalApp (MC.UExt val rep1))) <- return r1
  PC.Refl <- PC.testEquality rep1 (NR.knownNat @65)
  case MT.typeRepr val of
    MT.BVTypeRepr valwidth ->
      case PC.testEquality valwidth targetSize of
        Nothing -> Nothing
        Just PC.Refl -> do
          let newConstant = MC.mkLit targetSize constantVal
          return (MC.BVAdd targetSize val newConstant)

simplifyTrivialTruncExt :: MC.App (MC.Value ARM.AArch32 ids) tp
                        -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyTrivialTruncExt r3 = do
  MC.Trunc r2 rep3 <- return r3
  let targetSize = NR.knownNat @32
  PC.Refl <- PC.testEquality rep3 targetSize
  MC.AssignedValue (MC.Assignment _r1_id (MC.EvalApp (MC.UExt val rep1))) <- return r2
  PC.Refl <- PC.testEquality rep1 (NR.knownNat @65)
  case MT.typeRepr val of
    MT.BVTypeRepr valwidth ->
      case PC.testEquality valwidth targetSize of
        Nothing -> Nothing
        Just PC.Refl -> do
          let newConstant = MC.BVValue targetSize (NR.toSigned targetSize 0)
          return (MC.BVAdd targetSize val newConstant)

-- | Coalesce adjacent additions by a constant
--
-- > r2 := (bv_add r1 (0xfffffffb :: [65]))
-- > r3 := (bv_add r2 (0x1 :: [65]))
coalesceAdditionByConstant :: MC.App (MC.Value ARM.AArch32 ids) tp
                           -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
coalesceAdditionByConstant r3 = do
  MC.BVAdd rep3 r2 (MC.BVValue _bvrep3 c3) <- return r3
  MC.AssignedValue (MC.Assignment _ (MC.EvalApp (MC.BVAdd _rep2 r1 (MC.BVValue bvrep2 c2)))) <- return r2
  let newConstant = MC.mkLit bvrep2 (c2 + c3)
  return (MC.BVAdd rep3 r1 newConstant)

-- | Around conditional branches, we generate nested muxes that have the same conditions.
--
-- This code eliminates the redundancy (and happens to make the resulting IP
-- muxes match macaw's expectations to identify conditional branches)
--
-- > r1 := (mux _repr cond1 true1 false1)
-- > r2 := (mux _repr cond2 true2 false2)
-- > r3 := (mux repr cond3 r1 r2)
--
-- If the conditions are all equal, rewrite this into
--
-- > r3 := (mux repr cond3 true1 false2)
simplifyNestedMux :: MC.App (MC.Value ARM.AArch32 ids) tp
                  -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
simplifyNestedMux app = do
  MC.Mux repr3 cond3 r1 r2 <- return app
  MC.Mux _repr2 cond2 _true2 false2 <- MC.valueAsApp r2
  MC.Mux _repr1 cond1 true1 _false1 <- MC.valueAsApp r1
  PC.Refl <- PC.testEquality cond1 cond3
  PC.Refl <- PC.testEquality cond2 cond3
  return (MC.Mux repr3 cond3 true1 false2)

withConstantFirst :: MC.Value ARM.AArch32 ids tp
                  -> MC.Value ARM.AArch32 ids tp
                  -> Maybe (MC.Value ARM.AArch32 ids tp, Maybe (MC.App (MC.Value ARM.AArch32 ids) tp))
withConstantFirst l r =
  case (l, r) of
    (MC.BVValue {}, _) -> Just (l, MC.valueAsApp r)
    (_, MC.BVValue {}) -> Just (r, MC.valueAsApp l)
    _ -> Nothing

-- | Distribute an addition over a mux of constant addresses
--
-- There is a common pattern in conditional branches where the branch targets
-- are hidden under a constant addition.  This pushes the addition down.
distributeAddOverConstantMux :: MC.App (MC.Value ARM.AArch32 ids) tp
                             -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
distributeAddOverConstantMux app = do
  MC.BVAdd rep l r <- return app
  PC.Refl <- PC.testEquality rep (NR.knownNat @32)
  (MC.BVValue crep c, Just (MC.Mux mrep cond t f)) <- withConstantFirst l r
  MC.RelocatableValue trep taddr <- return t
  MC.RelocatableValue frep faddr <- return f
  let cval = NR.toSigned crep c
  let taddr' = MC.incAddr cval taddr
  let faddr' = MC.incAddr cval faddr
  return (MC.Mux mrep cond (MC.RelocatableValue trep taddr') (MC.RelocatableValue frep faddr'))

-- Eliminate nested logical negations
doubleNegation :: MC.App (MC.Value ARM.AArch32 ids) tp
               -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
doubleNegation app = do
  MC.NotApp r1 <- return app
  MC.NotApp r2 <- MC.valueAsApp r1
  MC.valueAsApp r2


negatedTrivialMux :: MC.App (MC.Value ARM.AArch32 ids) tp
                  -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
negatedTrivialMux app = case app of
  MC.Mux _ cond (MC.BoolValue False) (MC.BoolValue True) ->
    case MSS.simplifyArchApp (MC.NotApp cond) of
      Just app' -> return app'
      _ -> return $ MC.NotApp cond
  _ -> Nothing

negatedMux :: MC.App (MC.Value ARM.AArch32 ids) tp
           -> Maybe (MC.App (MC.Value ARM.AArch32 ids) tp)
negatedMux app = do
  MC.Mux rep c l r <- return app
  MC.NotApp c' <- MC.valueAsApp c
  return $ MC.Mux rep c' r l
