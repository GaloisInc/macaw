{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
-- | Instance definitions to assist in extracting Macaw values from instruction operands
--
-- This module is full of orphans, as the definitions of the classes are in a
-- package that cannot depend on the architecture-specific backends.
module Data.Macaw.PPC.Operand () where

import           Control.Lens ( (^.) )

import qualified Data.BitVector.Sized as BV
import qualified Data.Parameterized.NatRepr as NR
import qualified Data.Macaw.CFG.Core as MC
import           Data.Macaw.Types
import qualified Dismantle.PPC as D
import           GHC.TypeLits ( type (<=) )

import qualified SemMC.Architecture.PPC as PPC
import           Data.Macaw.SemMC.Operands
import qualified Data.Macaw.PPC.PPCReg as R

instance (w ~ PPC.AddrWidth v, 1 <= w) => ExtractValue (PPC.AnyPPC v) D.GPR (BVType w) where
  extractValue regs gpr = regs ^. MC.boundValue (R.PPC_GP gpr)

instance (PPC.KnownVariant v, w ~ PPC.AddrWidth v) => ExtractValue (PPC.AnyPPC v) (Maybe D.GPR) (BVType w) where
  extractValue regs mgpr =
    case mgpr of
      Just gpr -> extractValue regs gpr
      Nothing -> MC.BVValue w (BV.zero w)
        where w = PPC.addrWidth (PPC.knownVariant @v)

instance ExtractValue (PPC.AnyPPC v) D.FR (BVType 128) where
  extractValue regs (D.FR fr) = regs ^. MC.boundValue (R.PPC_FR (D.VSReg fr))

instance ExtractValue (PPC.AnyPPC v) D.VR (BVType 128) where
  extractValue regs (D.VR vr) = regs ^. MC.boundValue (R.PPC_FR (D.VSReg (vr + 32)))

instance ExtractValue (PPC.AnyPPC v) D.VSReg (BVType 128) where
  extractValue regs (D.VSReg vsr) = regs ^. MC.boundValue (R.PPC_FR (D.VSReg vsr))

instance ExtractValue (PPC.AnyPPC v) D.AbsBranchTarget (BVType 24) where
  extractValue _ (D.ABT w) = MC.BVValue NR.knownNat (toBV w)

instance ExtractValue (PPC.AnyPPC v) D.CondBranchTarget (BVType 14) where
  extractValue _ (D.CBT i) = MC.BVValue NR.knownNat (toBV i)

instance ExtractValue (PPC.AnyPPC v) D.AbsCondBranchTarget (BVType 14) where
  extractValue _ (D.ACBT w) = MC.BVValue NR.knownNat (toBV w)

instance ExtractValue (PPC.AnyPPC v) D.BranchTarget (BVType 24) where
  extractValue _ (D.BT i) = MC.BVValue NR.knownNat (toBV i)

instance ExtractValue (PPC.AnyPPC v) D.CRBitM (BVType 4) where
  extractValue _ (D.CRBitM b) = MC.BVValue NR.knownNat (toBV b)

instance ExtractValue (PPC.AnyPPC v) D.CRBitRC (BVType 5) where
  extractValue _ (D.CRBitRC b) = MC.BVValue NR.knownNat (toBV b)

instance ExtractValue (PPC.AnyPPC v) D.CRRC (BVType 3) where
  extractValue _ (D.CRRC b) = MC.BVValue NR.knownNat (toBV b)

instance (PPC.KnownVariant v, w ~ PPC.AddrWidth v) => ToRegister D.GPR (R.PPCReg v) (BVType w) where
  toRegister = R.PPC_GP

instance ToRegister D.FR (R.PPCReg v) (BVType 128) where
  toRegister (D.FR rnum) = R.PPC_FR (D.VSReg rnum)

instance ToRegister D.VR (R.PPCReg v) (BVType 128) where
  toRegister (D.VR vrnum) = R.PPC_FR (D.VSReg (vrnum + 32))

instance ToRegister D.VSReg (R.PPCReg v) (BVType 128) where
  toRegister = R.PPC_FR

-- | Convert to a bitvector
toBV :: (Integral a, KnownNat w) => a -> BV.BV w
toBV i = BV.mkBV NR.knownNat (toInteger i)
