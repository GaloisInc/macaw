{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE TypeApplications      #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.PPC.Arch (
  PPCTermStmt(..),
  rewriteTermStmt,
  PPCStmt(..),
  rewriteStmt,
  PPCPrimFn(..),
  rewritePrimFn,
  ppcPrimFnHasSideEffects,
  PPCArchConstraints,
  ppcInstructionMatcher
  ) where

import           GHC.TypeLits

import           Control.Lens ( (^.) )
import           Data.Bits
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import           Data.Parameterized.Classes ( knownRepr )
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MC
import           Data.Macaw.CFG.Rewriter ( Rewriter, rewriteValue, evalRewrittenArchFn, appendRewrittenArchStmt )
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT

import qualified Dismantle.PPC as D
import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64
import qualified SemMC.Architecture.PPC as SP
import qualified SemMC.Architecture.PPC.Eval as E

import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import           Data.Macaw.PPC.Operand ()
import           Data.Macaw.PPC.PPCReg

data PPCTermStmt ppc ids where
  -- | A representation of the PowerPC @sc@ instruction
  --
  -- That instruction technically takes an argument, but it must be zero so we
  -- don't preserve it.
  PPCSyscall :: PPCTermStmt ppc ids
  -- | A non-syscall trap initiated by the @td@, @tw@, @tdi@, or @twi@ instructions
  PPCTrap :: PPCTermStmt ppc ids
  -- | A conditional trap
  PPCTrapdword :: MC.Value ppc ids (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
               -> MC.Value ppc ids (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
               -> MC.Value ppc ids (MT.BVType 5)
               -> PPCTermStmt ppc ids

instance (MC.RegisterInfo (MC.ArchReg ppc)) => Show (PPCTermStmt ppc ids) where
  show ts = show (MC.prettyF ts)

type instance MC.ArchTermStmt PPC64.PPC = PPCTermStmt PPC64.PPC
type instance MC.ArchTermStmt PPC32.PPC = PPCTermStmt PPC32.PPC

instance (MC.RegisterInfo (MC.ArchReg ppc)) => MC.PrettyF (PPCTermStmt ppc) where
  prettyF ts =
    case ts of
      PPCSyscall -> PP.text "ppc_syscall"
      PPCTrap -> PP.text "ppc_trap"
      PPCTrapdword vb va vto -> PP.text "ppc_trapdword" PP.<+> MC.ppValue 0 vb PP.<+> MC.ppValue 0 va PP.<+> MC.ppValue 0 vto

rewriteTermStmt :: PPCTermStmt ppc src -> Rewriter ppc s src tgt (PPCTermStmt ppc tgt)
rewriteTermStmt s =
  case s of
    PPCSyscall -> return PPCSyscall
    PPCTrap -> return PPCTrap
    PPCTrapdword vb va vto -> PPCTrapdword <$> rewriteValue vb <*> rewriteValue va <*> rewriteValue vto

data PPCStmt ppc (v :: MT.Type -> *) where
  Attn :: PPCStmt ppc v
  Sync :: PPCStmt ppc v
  Isync :: PPCStmt ppc v
  -- These are data cache hints
  Dcba   :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> PPCStmt ppc v
  Dcbf   :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> PPCStmt ppc v
  Dcbi   :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> PPCStmt ppc v
  Dcbst  :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> PPCStmt ppc v
  Dcbz   :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> PPCStmt ppc v
  Dcbzl  :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> PPCStmt ppc v
  Dcbt   :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> v (MT.BVType 5) -> PPCStmt ppc v
  Dcbtst :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> v (MT.BVType 5) -> PPCStmt ppc v
  -- Instruction cache hints
  Icbi :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> PPCStmt ppc v
  Icbt :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> v (MT.BVType 4) -> PPCStmt ppc v
  -- Hardware Transactional Memory
  Tabort :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc))) -> PPCStmt ppc v
  Tabortdc :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
           -> v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
           -> v (MT.BVType 5)
           -> PPCStmt ppc v
  Tabortdci :: v (MT.BVType 5)
            -> v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
            -> v (MT.BVType 5)
            -> PPCStmt ppc v
  Tabortwc :: v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
           -> v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
           -> v (MT.BVType 5)
           -> PPCStmt ppc v
  Tabortwci :: v (MT.BVType 5)
            -> v (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
            -> v (MT.BVType 5)
            -> PPCStmt ppc v
  Tbegin :: v (MT.BVType 1) -> PPCStmt ppc v
  Tcheck :: v (MT.BVType 3) -> PPCStmt ppc v
  Tend :: v (MT.BVType 1) -> PPCStmt ppc v

instance TF.FunctorF (PPCStmt ppc) where
  fmapF = TF.fmapFDefault

instance TF.FoldableF (PPCStmt ppc) where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF (PPCStmt ppc) where
  traverseF go stmt =
    case stmt of
      Attn -> pure Attn
      Sync -> pure Sync
      Isync -> pure Isync
      Dcba ea -> Dcba <$> go ea
      Dcbf ea -> Dcbf <$> go ea
      Dcbi ea -> Dcbi <$> go ea
      Dcbst ea -> Dcbst <$> go ea
      Dcbz ea -> Dcbz <$> go ea
      Dcbzl ea -> Dcbzl <$> go ea
      Dcbt ea th -> Dcbt <$> go ea <*> go th
      Dcbtst ea th -> Dcbtst <$> go ea <*> go th
      Icbi ea -> Icbi <$> go ea
      Icbt ea ct -> Icbt <$> go ea <*> go ct
      Tabort r -> Tabort <$> go r
      Tabortdc r1 r2 v -> Tabortdc <$> go r1 <*> go r2 <*> go v
      Tabortdci v1 r v2 -> Tabortdci <$> go v1 <*> go r <*> go v2
      Tabortwc r1 r2 v -> Tabortwc <$> go r1 <*> go r2 <*> go v
      Tabortwci v1 r v2 -> Tabortwci <$> go v1 <*> go r <*> go v2
      Tbegin v -> Tbegin <$> go v
      Tcheck v -> Tcheck <$> go v
      Tend v -> Tend <$> go v

instance MC.IsArchStmt (PPCStmt ppc) where
  ppArchStmt pp stmt =
    case stmt of
      Attn -> PP.text "ppc_attn"
      Sync -> PP.text "ppc_sync"
      Isync -> PP.text "ppc_isync"
      Dcba ea -> PP.text "ppc_dcba" PP.<+> pp ea
      Dcbf ea -> PP.text "ppc_dcbf" PP.<+> pp ea
      Dcbi ea -> PP.text "ppc_dcbi" PP.<+> pp ea
      Dcbst ea -> PP.text "ppc_dcbst" PP.<+> pp ea
      Dcbz ea -> PP.text "ppc_dcbz" PP.<+> pp ea
      Dcbzl ea -> PP.text "ppc_dcbzl" PP.<+> pp ea
      Dcbt ea th -> PP.text "ppc_dcbt" PP.<+> pp ea PP.<+> pp th
      Dcbtst ea th -> PP.text "ppc_dcbtst" PP.<+> pp ea PP.<+> pp th
      Icbi ea -> PP.text "ppc_icbi" PP.<+> pp ea
      Icbt ea ct -> PP.text "ppc_icbt" PP.<+> pp ea PP.<+> pp ct
      Tabort r -> PP.text "ppc_tabort" PP.<+> pp r
      Tabortdc r1 r2 v -> PP.text "ppc_tabortdc" PP.<+> pp r1 PP.<+> pp r2 PP.<+> pp v
      Tabortdci v1 r v2 -> PP.text "ppc_tabortdci" PP.<+> pp v1 PP.<+> pp r PP.<+> pp v2
      Tabortwc r1 r2 v -> PP.text "ppc_tabortwc" PP.<+> pp r1 PP.<+> pp r2 PP.<+> pp v
      Tabortwci v1 r v2 -> PP.text "ppc_tabortwci" PP.<+> pp v1 PP.<+> pp r PP.<+> pp v2
      Tbegin v -> PP.text "ppc_tbegin" PP.<+> pp v
      Tcheck v -> PP.text "ppc_tcheck" PP.<+> pp v
      Tend v -> PP.text "ppc_tend" PP.<+> pp v

type instance MC.ArchStmt PPC64.PPC = PPCStmt PPC64.PPC
type instance MC.ArchStmt PPC32.PPC = PPCStmt PPC32.PPC

instance MC.IPAlignment PPC64.PPC where
  fromIPAligned cleanAddr
    | Just (MC.BVShl _ addrDiv4 two) <- MC.valueAsApp cleanAddr
    , MC.BVValue _ 2 <- two
    , Just smallAddrDiv4 <- valueAsExtTwo addrDiv4
    , Just (MC.Trunc addrDiv4' _) <- MC.valueAsApp smallAddrDiv4
    , Just NR.Refl <- NR.testEquality (MT.typeWidth addrDiv4') (MT.knownNat :: NR.NatRepr 64)
    , Just (MC.BVShr _ dirtyAddr two') <- MC.valueAsApp addrDiv4'
    , MC.BVValue _ 2 <- two'
    = Just dirtyAddr

    | Just (MC.BVAnd _ dirtyAddr (MC.BVValue _ 0xfffffffffffffffc)) <- MC.valueAsApp cleanAddr
    = Just dirtyAddr

    | Just (MC.BVAnd _ (MC.BVValue _ 0xfffffffffffffffc) dirtyAddr) <- MC.valueAsApp cleanAddr
    = Just dirtyAddr

    | otherwise = Nothing
    where
      valueAsExtTwo :: MC.BVValue PPC64.PPC ids 64 -> Maybe (MC.BVValue PPC64.PPC ids 62)
      valueAsExtTwo v
        | Just (MC.SExt v' _) <- MC.valueAsApp v
        , Just NR.Refl <- NR.testEquality (MT.typeWidth v') (MT.knownNat :: NR.NatRepr 62)
        = Just v'

        | Just (MC.UExt v' _) <- MC.valueAsApp v
        , Just NR.Refl <- NR.testEquality (MT.typeWidth v') (MT.knownNat :: NR.NatRepr 62)
        = Just v'

        | otherwise = Nothing

  toIPAligned addr = addr { MM.addrOffset = MM.addrOffset addr .&. complement 0x3 }

instance MC.IPAlignment PPC32.PPC where
  fromIPAligned _ = error "IP alignment rules are not yet implemented for PPC32"
  toIPAligned addr = addr { MM.addrOffset = MM.addrOffset addr .&. complement 0x3 }

rewriteStmt :: (MC.ArchStmt ppc ~ PPCStmt ppc) => PPCStmt ppc (MC.Value ppc src) -> Rewriter ppc s src tgt ()
rewriteStmt s = do
  s' <- TF.traverseF rewriteValue s
  appendRewrittenArchStmt s'

data PPCPrimFn ppc f tp where
  -- | Unsigned division
  --
  -- Division by zero does not have side effects, but instead produces an undefined value
  UDiv :: NR.NatRepr (MC.RegAddrWidth (MC.ArchReg ppc))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> PPCPrimFn ppc f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
  -- | Signed division
  --
  -- Division by zero does not have side effects, but instead produces an undefined value
  SDiv :: NR.NatRepr (MC.RegAddrWidth (MC.ArchReg ppc))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> PPCPrimFn ppc f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))

  -- | Interpreted floating point functions.
  FPNeg
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPAbs
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPSqrt
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)

  FPAdd
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPSub
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPMul
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPDiv
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPFMA
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)

  FPLt
    :: !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f MT.BoolType
  FPEq
    :: !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f MT.BoolType
  FPLe
    :: !(f (MT.FloatType fi))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f MT.BoolType

  FPIsNaN :: !(f (MT.FloatType fi)) -> PPCPrimFn ppc f MT.BoolType

  FPCast
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi'))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPRound
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi) 
  -- | Treat a floating-point as a bitvector.
  FPToBinary
    :: (1 <= MT.FloatInfoBits fi)
    => !(MT.FloatInfoRepr fi)
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.FloatBVType fi)
  -- | Treat a bitvector as a floating-point.
  FPFromBinary
    :: !(MT.FloatInfoRepr fi)
    -> !(f (MT.FloatBVType fi))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPToSBV
    :: (1 <= w)
    => !(MT.NatRepr w)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.BVType w)
  FPToUBV
    :: (1 <= w)
    => !(MT.NatRepr w)
    -> !(f (MT.BVType 2))
    -> !(f (MT.FloatType fi))
    -> PPCPrimFn ppc f (MT.BVType w)
  FPFromSBV
    :: (1 <= w)
    => !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.BVType w))
    -> PPCPrimFn ppc f (MT.FloatType fi)
  FPFromUBV
    :: (1 <= w)
    => !(MT.FloatInfoRepr fi)
    -> !(f (MT.BVType 2))
    -> !(f (MT.BVType w))
    -> PPCPrimFn ppc f (MT.FloatType fi)

  -- | Coerce a floating-point to another precision format without
  --   precision loss.
  FPCoerce
    :: !(MT.FloatInfoRepr fi)
    -> !(MT.FloatInfoRepr fi')
    -> !(f (MT.FloatType fi'))
    -> PPCPrimFn ppc f (MT.FloatType fi)

  -- | Uninterpreted floating point functions
  FPSCR1
    :: !String
    -> !(f (MT.BVType 128))
    -> !(f (MT.BVType 32))
    -> PPCPrimFn ppc f (MT.BVType 24)
  FPSCR2
    :: !String
    -> !(f (MT.BVType 128))
    -> !(f (MT.BVType 128))
    -> !(f (MT.BVType 32))
    -> PPCPrimFn ppc f (MT.BVType 24)
  FPSCR3
    :: !String
    -> !(f (MT.BVType 128))
    -> !(f (MT.BVType 128))
    -> !(f (MT.BVType 128))
    -> !(f (MT.BVType 32))
    -> PPCPrimFn ppc f (MT.BVType 24)

  -- | Uninterpreted floating point functions
  FP1 :: !String -- the name of the function
      -> !(f (MT.BVType 128)) -- arg 1
      -> !(f (MT.BVType 32)) -- current fpscr
      -> PPCPrimFn ppc f (MT.BVType 160)
  FP2 :: !String
      -> !(f (MT.BVType 128))
      -> !(f (MT.BVType 128))
      -> !(f (MT.BVType 32))
      -> PPCPrimFn ppc f (MT.BVType 160)
  FP3 :: !String
      -> !(f (MT.BVType 128))
      -> !(f (MT.BVType 128))
      -> !(f (MT.BVType 128))
      -> !(f (MT.BVType 32))
      -> PPCPrimFn ppc f (MT.BVType 160)

  -- | Uninterpreted vector functions
  Vec1 :: !String -- the name of the function
       -> !(f (MT.BVType 128))
       -> !(f (MT.BVType 32))
       -> PPCPrimFn ppc f (MT.BVType 160)
  Vec2 :: String -- the name of the function
       -> !(f (MT.BVType 128))
       -> !(f (MT.BVType 128))
       -> !(f (MT.BVType 32))
       -> PPCPrimFn ppc f (MT.BVType 160)
  Vec3 :: String -- the name of the function
       -> !(f (MT.BVType 128))
       -> !(f (MT.BVType 128))
       -> !(f (MT.BVType 128))
       -> !(f (MT.BVType 32))
       -> PPCPrimFn ppc f (MT.BVType 160)

instance (1 <= MC.RegAddrWidth (MC.ArchReg ppc)) => MT.HasRepr (PPCPrimFn ppc v) MT.TypeRepr where
  typeRepr = \case
    UDiv rep _ _ -> MT.BVTypeRepr rep
    SDiv rep _ _ -> MT.BVTypeRepr rep

    FPNeg  fi _      -> MT.FloatTypeRepr fi
    FPAbs  fi _      -> MT.FloatTypeRepr fi
    FPSqrt fi _ _    -> MT.FloatTypeRepr fi
    FPAdd fi _ _ _   -> MT.FloatTypeRepr fi
    FPSub fi _ _ _   -> MT.FloatTypeRepr fi
    FPMul fi _ _ _   -> MT.FloatTypeRepr fi
    FPDiv fi _ _ _   -> MT.FloatTypeRepr fi
    FPFMA fi _ _ _ _ -> MT.FloatTypeRepr fi
    FPLt{}    -> knownRepr
    FPEq{}    -> knownRepr
    FPLe{}    -> knownRepr
    FPIsNaN{} -> knownRepr
    FPCast       fi _ _ -> MT.FloatTypeRepr fi
    FPRound      fi _ _ -> MT.FloatTypeRepr fi
    FPToBinary   fi _   -> MT.floatBVTypeRepr fi
    FPFromBinary fi _   -> MT.FloatTypeRepr fi
    FPToSBV      w  _ _ -> MT.BVTypeRepr w
    FPToUBV      w  _ _ -> MT.BVTypeRepr w
    FPFromSBV    fi _ _ -> MT.FloatTypeRepr fi
    FPFromUBV    fi _ _ -> MT.FloatTypeRepr fi
    FPCoerce fi _ _ -> MT.FloatTypeRepr fi
    FPSCR1{} -> MT.BVTypeRepr MT.knownNat
    FPSCR2{} -> MT.BVTypeRepr MT.knownNat
    FPSCR3{} -> MT.BVTypeRepr MT.knownNat

    FP1{} -> MT.BVTypeRepr MT.knownNat
    FP2{} -> MT.BVTypeRepr MT.knownNat
    FP3{} -> MT.BVTypeRepr MT.knownNat

    Vec1{} -> MT.BVTypeRepr MT.knownNat
    Vec2{} -> MT.BVTypeRepr MT.knownNat
    Vec3{} -> MT.BVTypeRepr MT.knownNat

-- | Right now, none of the primitive functions has a side effect.  That will
-- probably change.
ppcPrimFnHasSideEffects :: PPCPrimFn ppc f tp -> Bool
ppcPrimFnHasSideEffects = \case
  UDiv{}         -> False
  SDiv{}         -> False
  FPNeg{}        -> False
  FPAbs{}        -> False
  FPSqrt{}       -> False
  FPAdd{}        -> False
  FPSub{}        -> False
  FPMul{}        -> False
  FPDiv{}        -> False
  FPFMA{}        -> False
  FPLt{}         -> False
  FPEq{}         -> False
  FPLe{}         -> False
  FPIsNaN{}      -> False
  FPCast{}       -> False
  FPRound{}      -> False
  FPToBinary{}   -> False
  FPFromBinary{} -> False
  FPToSBV{}      -> False
  FPToUBV{}      -> False
  FPFromSBV{}    -> False
  FPFromUBV{}    -> False
  FPCoerce{}     -> False
  FPSCR1{}       -> False
  FPSCR2{}       -> False
  FPSCR3{}       -> False
  FP1{}          -> False
  FP2{}          -> False
  FP3{}          -> False
  Vec1{}         -> False
  Vec2{}         -> False
  Vec3{}         -> False

rewritePrimFn :: ( ppc ~ SP.AnyPPC var
                 , PPCArchConstraints var
                 , MC.ArchFn ppc ~ PPCPrimFn ppc
                 )
              => PPCPrimFn ppc (MC.Value ppc src) tp
              -> Rewriter ppc s src tgt (MC.Value ppc tgt tp)
rewritePrimFn = \case
  UDiv rep lhs rhs -> do
    tgtFn <- UDiv rep <$> rewriteValue lhs <*> rewriteValue rhs
    evalRewrittenArchFn tgtFn
  SDiv rep lhs rhs -> do
    tgtFn <- SDiv rep <$> rewriteValue lhs <*> rewriteValue rhs
    evalRewrittenArchFn tgtFn
  FPNeg  fi x -> evalRewrittenArchFn =<< (FPNeg fi <$> rewriteValue x)
  FPAbs  fi x -> evalRewrittenArchFn =<< (FPAbs fi <$> rewriteValue x)
  FPSqrt fi r x ->
    evalRewrittenArchFn =<< (FPSqrt fi <$> rewriteValue r <*> rewriteValue x)
  FPAdd fi r x y ->
    evalRewrittenArchFn
      =<< (FPAdd fi <$> rewriteValue r <*> rewriteValue x <*> rewriteValue y)
  FPSub fi r x y ->
    evalRewrittenArchFn
      =<< (FPSub fi <$> rewriteValue r <*> rewriteValue x <*> rewriteValue y)
  FPMul fi r x y ->
    evalRewrittenArchFn
      =<< (FPMul fi <$> rewriteValue r <*> rewriteValue x <*> rewriteValue y)
  FPDiv fi r x y ->
    evalRewrittenArchFn
      =<< (FPDiv fi <$> rewriteValue r <*> rewriteValue x <*> rewriteValue y)
  FPFMA fi r x y z ->
    evalRewrittenArchFn
      =<< (FPFMA fi <$> rewriteValue r <*> rewriteValue x <*> rewriteValue y <*> rewriteValue z)
  FPLt x y ->
    evalRewrittenArchFn =<< (FPLt <$> rewriteValue x <*> rewriteValue y)
  FPEq x y ->
    evalRewrittenArchFn =<< (FPEq <$> rewriteValue x <*> rewriteValue y)
  FPLe x y ->
    evalRewrittenArchFn =<< (FPLe <$> rewriteValue x <*> rewriteValue y)
  FPIsNaN x -> evalRewrittenArchFn =<< (FPIsNaN <$> rewriteValue x)
  FPCast fi r x ->
    evalRewrittenArchFn =<< (FPCast fi <$> rewriteValue r <*> rewriteValue x)
  FPRound fi r x ->
    evalRewrittenArchFn =<< (FPRound fi <$> rewriteValue r <*> rewriteValue x)
  FPToBinary fi x -> evalRewrittenArchFn =<< (FPToBinary fi <$> rewriteValue x)
  FPFromBinary fi x ->
    evalRewrittenArchFn =<< (FPFromBinary fi <$> rewriteValue x)
  FPToSBV w r x ->
    evalRewrittenArchFn =<< (FPToSBV w <$> rewriteValue r <*> rewriteValue x)
  FPToUBV w r x ->
    evalRewrittenArchFn =<< (FPToUBV w <$> rewriteValue r <*> rewriteValue x)
  FPFromSBV fi r x ->
    evalRewrittenArchFn =<< (FPFromSBV fi <$> rewriteValue r <*> rewriteValue x)
  FPFromUBV fi r x ->
    evalRewrittenArchFn =<< (FPFromUBV fi <$> rewriteValue r <*> rewriteValue x)
  FPCoerce fi fi' x -> evalRewrittenArchFn =<< (FPCoerce fi fi' <$> rewriteValue x)
  FPSCR1 name op fpscr ->
    evalRewrittenArchFn =<< (FPSCR1 name <$> rewriteValue op <*> rewriteValue fpscr)
  FPSCR2 name op1 op2 fpscr ->
    evalRewrittenArchFn =<< (FPSCR2 name <$> rewriteValue op1 <*> rewriteValue op2 <*> rewriteValue fpscr)
  FPSCR3 name op1 op2 op3 fpscr ->
    evalRewrittenArchFn =<< (FPSCR3 name <$> rewriteValue op1 <*> rewriteValue op2 <*> rewriteValue op3 <*> rewriteValue fpscr)
  FP1 name op fpscr -> do
    tgtFn <- FP1 name <$> rewriteValue op <*> rewriteValue fpscr
    evalRewrittenArchFn tgtFn
  FP2 name op1 op2 fpscr -> do
    tgtFn <- FP2 name <$> rewriteValue op1 <*> rewriteValue op2 <*> rewriteValue fpscr
    evalRewrittenArchFn tgtFn
  FP3 name op1 op2 op3 fpscr -> do
    tgtFn <- FP3 name <$> rewriteValue op1 <*> rewriteValue op2 <*> rewriteValue op3 <*> rewriteValue fpscr
    evalRewrittenArchFn tgtFn
  Vec1 name op vscr -> do
    tgtFn <- Vec1 name <$> rewriteValue op <*> rewriteValue vscr
    evalRewrittenArchFn tgtFn
  Vec2 name op1 op2 vscr -> do
    tgtFn <- Vec2 name <$> rewriteValue op1 <*> rewriteValue op2 <*> rewriteValue vscr
    evalRewrittenArchFn tgtFn
  Vec3 name op1 op2 op3 vscr -> do
    tgtFn <- Vec3 name <$> rewriteValue op1 <*> rewriteValue op2 <*> rewriteValue op3 <*> rewriteValue vscr
    evalRewrittenArchFn tgtFn

ppPrimFn :: (Applicative m) => (forall u . f u -> m PP.Doc) -> PPCPrimFn ppc f tp -> m PP.Doc
ppPrimFn pp = \case
  UDiv _ lhs rhs -> ppBinary "ppc_udiv" <$> pp lhs <*> pp rhs
  SDiv _ lhs rhs -> ppBinary "ppc_sdiv" <$> pp lhs <*> pp rhs
  FPNeg _fi x -> ppUnary "ppc_fp_neg" <$> pp x
  FPAbs _fi x -> ppUnary "ppc_fp_abs" <$> pp x
  FPSqrt _fi r x -> ppBinary "ppc_fp_sqrt" <$> pp r <*> pp x
  FPAdd _fi r x y -> pp3 "ppc_fp_add" <$> pp r <*> pp x <*> pp y
  FPSub _fi r x y -> pp3 "ppc_fp_sub" <$> pp r <*> pp x <*> pp y
  FPMul _fi r x y -> pp3 "ppc_fp_mul" <$> pp r <*> pp x <*> pp y
  FPDiv _fi r x y -> pp3 "ppc_fp_div" <$> pp r <*> pp x <*> pp y
  FPFMA _fi r x y z -> pp4 "ppc_fp_fma" <$> pp r <*> pp x <*> pp y <*> pp z
  FPLt x y -> ppBinary "ppc_fp_lt" <$> pp x <*> pp y
  FPEq x y -> ppBinary "ppc_fp_eq" <$> pp x <*> pp y
  FPLe x y -> ppBinary "ppc_fp_le" <$> pp x <*> pp y
  FPIsNaN x -> ppUnary "ppc_fp_is_nan" <$> pp x
  FPCast _fi r x -> ppBinary "ppc_fp_cast" <$> pp r <*> pp x
  FPRound _fi r x -> ppBinary "ppc_fp_round" <$> pp r <*> pp x
  FPToBinary   _fi x -> ppUnary "ppc_fp_to_binary" <$> pp x
  FPFromBinary _fi x -> ppUnary "ppc_fp_from_binary" <$> pp x
  FPToSBV   _w  r x -> ppBinary "ppc_fp_to_sbv" <$> pp r <*> pp x
  FPToUBV   _w  r x -> ppBinary "ppc_fp_to_ubv" <$> pp r <*> pp x
  FPFromSBV _fi r x -> ppBinary "ppc_fp_from_sbv" <$> pp r <*> pp x
  FPFromUBV _fi r x -> ppBinary "ppc_fp_from_ubv" <$> pp r <*> pp x
  FPCoerce _fi _fi' x -> ppUnary "ppc_fp_coerce" <$> pp x
  FPSCR1 n r1 fpscr -> ppBinary ("ppc_fp_un_op_fpscr " ++ n) <$> pp r1 <*> pp fpscr
  FPSCR2 n r1 r2 fpscr -> pp3 ("ppc_fp_bin_op_fpscr " ++ n) <$> pp r1 <*> pp r2 <*> pp fpscr
  FPSCR3 n r1 r2 r3 fpscr -> pp4 ("ppc_fp_tern_op_fpscr " ++ n) <$> pp r1 <*> pp r2 <*> pp r3 <*> pp fpscr
  FP1 n r1 fpscr -> ppBinary ("ppc_fp1 " ++ n) <$> pp r1 <*> pp fpscr
  FP2 n r1 r2 fpscr -> pp3 ("ppc_fp2 " ++ n) <$> pp r1 <*> pp r2 <*> pp fpscr
  FP3 n r1 r2 r3 fpscr -> pp4 ("ppc_fp3 " ++ n) <$> pp r1 <*> pp r2 <*> pp r3 <*> pp fpscr
  Vec1 n r1 vscr -> ppBinary ("ppc_vec1 " ++ n) <$> pp r1 <*> pp vscr
  Vec2 n r1 r2 vscr -> pp3 ("ppc_vec2" ++ n) <$> pp r1 <*> pp r2 <*> pp vscr
  Vec3 n r1 r2 r3 vscr -> pp4 ("ppc_vec3" ++ n) <$> pp r1 <*> pp r2 <*> pp r3 <*> pp vscr
 where
  ppUnary s v' = PP.text s PP.<+> v'
  ppBinary s v1' v2' = PP.text s PP.<+> v1' PP.<+> v2'
  pp3 s v1' v2' v3' = PP.text s PP.<+> v1' PP.<+> v2' PP.<+> v3'
  pp4 s v1' v2' v3' v4' = PP.text s PP.<+> v1' PP.<+> v2' PP.<+> v3' PP.<+> v4'

instance MC.IsArchFn (PPCPrimFn ppc) where
  ppArchFn = ppPrimFn

instance FC.FunctorFC (PPCPrimFn ppc) where
  fmapFC = FC.fmapFCDefault

instance FC.FoldableFC (PPCPrimFn ppc) where
  foldMapFC = FC.foldMapFCDefault

instance FC.TraversableFC (PPCPrimFn ppc) where
  traverseFC go = \case
    UDiv rep lhs rhs -> UDiv rep <$> go lhs <*> go rhs
    SDiv rep lhs rhs -> SDiv rep <$> go lhs <*> go rhs
    FPNeg  fi x -> FPNeg fi <$> go x
    FPAbs  fi x -> FPAbs fi <$> go x
    FPSqrt fi r x -> FPSqrt fi <$> go r <*> go x
    FPAdd fi r x y -> FPAdd fi <$> go r <*> go x <*> go y
    FPSub fi r x y -> FPSub fi <$> go r <*> go x <*> go y
    FPMul fi r x y -> FPMul fi <$> go r <*> go x <*> go y
    FPDiv fi r x y -> FPDiv fi <$> go r <*> go x <*> go y
    FPFMA fi r x y z -> FPFMA fi <$> go r <*> go x <*> go y <*> go z
    FPLt x y -> FPLt <$> go x <*> go y
    FPEq x y -> FPEq <$> go x <*> go y
    FPLe x y -> FPLe <$> go x <*> go y
    FPIsNaN x -> FPIsNaN <$> go x
    FPCast fi r x -> FPCast fi <$> go r <*> go x
    FPRound fi r x -> FPRound fi <$> go r <*> go x
    FPToBinary   fi x -> FPToBinary fi <$> go x
    FPFromBinary fi x -> FPFromBinary fi <$> go x
    FPToSBV   w  r x -> FPToSBV w <$> go r <*> go x
    FPToUBV   w  r x -> FPToUBV w <$> go r <*> go x
    FPFromSBV fi r x -> FPFromSBV fi <$> go r <*> go x
    FPFromUBV fi r x -> FPFromUBV fi <$> go r <*> go x
    FPCoerce fi fi' x -> FPCoerce fi fi' <$> go x
    FPSCR1 name op fpscr -> FPSCR1 name <$> go op <*> go fpscr
    FPSCR2 name op1 op2 fpscr -> FPSCR2 name <$> go op1 <*> go op2 <*> go fpscr
    FPSCR3 name op1 op2 op3 fpscr -> FPSCR3 name <$> go op1 <*> go op2 <*> go op3 <*> go fpscr
    FP1 name op fpscr -> FP1 name <$> go op <*> go fpscr
    FP2 name op1 op2 fpscr -> FP2 name <$> go op1 <*> go op2 <*> go fpscr
    FP3 name op1 op2 op3 fpscr -> FP3 name <$> go op1 <*> go op2 <*> go op3 <*> go fpscr
    Vec1 name op vscr -> Vec1 name <$> go op <*> go vscr
    Vec2 name op1 op2 vscr -> Vec2 name <$> go op1 <*> go op2 <*> go vscr
    Vec3 name op1 op2 op3 vscr -> Vec3 name <$> go op1 <*> go op2 <*> go op3 <*> go vscr

type instance MC.ArchFn PPC64.PPC = PPCPrimFn PPC64.PPC
type instance MC.ArchFn PPC32.PPC = PPCPrimFn PPC32.PPC

type PPCArchConstraints var = ( MC.ArchReg (SP.AnyPPC var) ~ PPCReg (SP.AnyPPC var)
                              , MC.ArchFn (SP.AnyPPC var) ~ PPCPrimFn (SP.AnyPPC var)
                              , MC.ArchStmt (SP.AnyPPC var) ~ PPCStmt (SP.AnyPPC var)
                              , MC.ArchTermStmt (SP.AnyPPC var) ~ PPCTermStmt (SP.AnyPPC var)
                              , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg (SP.AnyPPC var)))
                              , 1 <= MC.RegAddrWidth (PPCReg (SP.AnyPPC var))
                              , KnownNat (MC.RegAddrWidth (PPCReg (SP.AnyPPC var)))
                              , SP.KnownVariant var
                              , MC.ArchConstraints (SP.AnyPPC var)
                              , O.ExtractValue (SP.AnyPPC var) D.GPR (MT.BVType (MC.RegAddrWidth (MC.ArchReg (SP.AnyPPC var))))
                              , O.ExtractValue (SP.AnyPPC var) (Maybe D.GPR) (MT.BVType (MC.RegAddrWidth (MC.ArchReg (SP.AnyPPC var))))
                              )

memrrToEffectiveAddress :: forall var ppc ids s n
                         . (ppc ~ SP.AnyPPC var
                           , n ~ MC.RegAddrWidth (MC.ArchReg ppc)
                           , PPCArchConstraints var
                           )
                        => MC.RegState (PPCReg ppc) (MC.Value ppc ids)
                        -> D.MemRR
                        -> G.Generator ppc ids s (MC.Value ppc ids (MT.BVType n))
memrrToEffectiveAddress regs memrr = do
  let offset = O.extractValue regs (E.interpMemrrOffsetExtractor memrr)
  let base = O.extractValue regs (E.interpMemrrBaseExtractor memrr)
  let isr0 = O.extractValue regs (E.interpIsR0 (E.interpMemrrBaseExtractor memrr))
  let repr = MT.knownNat @n
  let zero = MC.BVValue repr 0
  b <- G.addExpr (G.AppExpr (MC.Mux (MT.BVTypeRepr repr) isr0 zero base))
  G.addExpr (G.AppExpr (MC.BVAdd repr b offset))

-- | A helper to increment the IP by 4, meant to be used to implement
-- arch-specific statements that need to update the IP (i.e., all but syscalls).
incrementIP :: (PPCArchConstraints var) => G.Generator (SP.AnyPPC var) ids s ()
incrementIP = do
  rs <- G.getRegs
  let ipVal = rs ^. MC.boundValue PPC_IP
  e <- G.addExpr (G.AppExpr (MC.BVAdd knownRepr ipVal (MC.BVValue knownRepr 0x4)))
  G.setRegVal PPC_IP e

-- | Manually-provided semantics for instructions whose full semantics cannot be
-- expressed in our semantics format.
--
-- This includes instructions with special side effects that we don't have a way
-- to talk about in the semantics; especially useful for architecture-specific
-- terminator statements.
--
-- NOTE: For SC and TRAP (which we treat as system calls), we don't need to
-- update the IP here, as the update is handled in the abstract interpretation
-- of system calls in 'postPPCTermStmtAbsState'.
ppcInstructionMatcher :: forall var ppc ids s n
                       . ( ppc ~ SP.AnyPPC var
                         , PPCArchConstraints var
                         , n ~ MC.ArchAddrWidth ppc
                         , 17 <= n
                         )
                      => D.Instruction
                      -> Maybe (G.Generator ppc ids s ())
ppcInstructionMatcher (D.Instruction opc operands) =
  case opc of
    D.SC -> Just $ G.finishWithTerminator (MC.ArchTermStmt PPCSyscall)
    D.TRAP -> Just $ G.finishWithTerminator (MC.ArchTermStmt PPCTrap)
    D.TD ->
      case operands of
        D.Gprc rB D.:< D.Gprc rA D.:< D.U5imm to D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          let vB = O.extractValue regs rB
          let vA = O.extractValue regs rA
          let vTo = O.extractValue regs to
          G.finishWithTerminator (MC.ArchTermStmt (PPCTrapdword vB vA vTo))
    D.TDI ->
      case operands of
        D.S16imm imm D.:< D.Gprc rA D.:< D.U5imm to D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          let vB = O.extractValue regs imm
          let repr = MT.knownNat @n
          vB' <- G.addExpr (G.AppExpr (MC.SExt vB repr))
          let vA = O.extractValue regs rA
          let vTo = O.extractValue regs to
          G.finishWithTerminator (MC.ArchTermStmt (PPCTrapdword vB' vA vTo))
    D.ATTN -> Just $ do
      incrementIP
      G.addStmt (MC.ExecArchStmt Attn)
    D.SYNC -> Just $ do
      incrementIP
      G.addStmt (MC.ExecArchStmt Sync)
    D.ISYNC -> Just $ do
      incrementIP
      G.addStmt (MC.ExecArchStmt Isync)
    D.DCBA ->
      case operands of
        D.Memrr memrr D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          G.addStmt (MC.ExecArchStmt (Dcba ea))
    D.DCBF ->
      case operands of
        D.Memrr memrr D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          G.addStmt (MC.ExecArchStmt (Dcbf ea))
    D.DCBI ->
      case operands of
        D.Memrr memrr D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          G.addStmt (MC.ExecArchStmt (Dcbi ea))
    D.DCBST ->
      case operands of
        D.Memrr memrr D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          G.addStmt (MC.ExecArchStmt (Dcbst ea))
    D.DCBZ ->
      case operands of
        D.Memrr memrr D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          G.addStmt (MC.ExecArchStmt (Dcbz ea))
    D.DCBZL ->
      case operands of
        D.Memrr memrr D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          G.addStmt (MC.ExecArchStmt (Dcbzl ea))
    D.DCBT ->
      case operands of
        D.Memrr memrr D.:< D.U5imm imm D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          let th = O.extractValue regs imm
          G.addStmt (MC.ExecArchStmt (Dcbt ea th))
    D.DCBTST ->
      case operands of
        D.Memrr memrr D.:< D.U5imm imm D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          let th = O.extractValue regs imm
          G.addStmt (MC.ExecArchStmt (Dcbtst ea th))
    D.ICBI ->
      case operands of
        D.Memrr memrr D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          G.addStmt (MC.ExecArchStmt (Icbi ea))
    D.ICBT ->
      case operands of
        D.Memrr memrr D.:< D.U4imm imm D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          ea <- memrrToEffectiveAddress regs memrr
          let ct = O.extractValue regs imm
          G.addStmt (MC.ExecArchStmt (Icbt ea ct))
    D.TABORT ->
      case operands of
        D.Gprc r D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          let rv = O.extractValue regs r
          G.addStmt (MC.ExecArchStmt (Tabort rv))
    D.TABORTDC ->
      case operands of
        D.Gprc r1 D.:< D.Gprc r2 D.:< D.U5imm imm D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          let rv1 = O.extractValue regs r1
          let rv2 = O.extractValue regs r2
          let immv = O.extractValue regs imm
          G.addStmt (MC.ExecArchStmt (Tabortdc rv1 rv2 immv))
    D.TABORTDCI ->
      case operands of
        D.U5imm i1 D.:< D.Gprc r D.:< D.U5imm i2 D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          let imm1 = O.extractValue regs i1
          let rv = O.extractValue regs r
          let imm2 = O.extractValue regs i2
          G.addStmt (MC.ExecArchStmt (Tabortdci imm1 rv imm2))
    D.TABORTWC ->
      case operands of
        D.Gprc r1 D.:< D.Gprc r2 D.:< D.U5imm imm D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          let rv1 = O.extractValue regs r1
          let rv2 = O.extractValue regs r2
          let immv = O.extractValue regs imm
          G.addStmt (MC.ExecArchStmt (Tabortwc rv1 rv2 immv))
    D.TABORTWCI ->
      case operands of
        D.U5imm i1 D.:< D.Gprc r D.:< D.U5imm i2 D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          let imm1 = O.extractValue regs i1
          let rv = O.extractValue regs r
          let imm2 = O.extractValue regs i2
          G.addStmt (MC.ExecArchStmt (Tabortwci imm1 rv imm2))
    D.TBEGIN ->
      case operands of
        D.U1imm i D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          let iv = O.extractValue regs i
          G.addStmt (MC.ExecArchStmt (Tbegin iv))
    D.TCHECK ->
      case operands of
        D.Crrc r D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          let rv = O.extractValue regs r
          G.addStmt (MC.ExecArchStmt (Tcheck rv))
    D.TEND ->
      case operands of
        D.U1imm i D.:< D.Nil -> Just $ do
          regs <- G.getRegs
          incrementIP
          let iv = O.extractValue regs i
          G.addStmt (MC.ExecArchStmt (Tend iv))
    _ -> Nothing
