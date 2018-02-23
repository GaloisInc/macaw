-- | Instance definitions to assist in extracting Macaw values from instruction operands
--
-- This module is full of orphans, as the definitions of the classes are in a
-- package that cannot depend on the architecture-specific backends.

{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}

module Data.Macaw.ARM.Operand
    (
    )
    where

import qualified Data.Macaw.ARM.ARMReg as Reg
import qualified Data.Macaw.CFG.Core as MC
import qualified Data.Macaw.SemMC.Generator as G
import           Data.Macaw.SemMC.Operands
import           Data.Macaw.Types ( BoolType, BVType )
import qualified Data.Parameterized.NatRepr as NR
import           Dismantle.ARM.Operands
import qualified SemMC.ARM as ARM


instance ExtractValue ARM.ARM GPR (BVType 32) where
  extractValue r = G.getRegValue (Reg.ARM_GP r)


instance ToRegister GPR Reg.ARMReg (BVType 32) where
  toRegister = Reg.ARM_GP


instance ExtractValue ARM.ARM (Maybe GPR) (BVType 32) where
  extractValue mgpr =
    case mgpr of
      Just r -> extractValue r
      Nothing -> return $ MC.BVValue NR.knownNat 0

instance ExtractValue ARM.ARM Pred (BVType 4) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . predToBits

instance ExtractValue ARM.ARM SBit (BVType 1) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . sBitToBits

instance ExtractValue ARM.ARM BranchExecuteTarget (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . branchExecuteTargetToBits

instance ExtractValue ARM.ARM SoRegImm (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . soRegImmToBits

instance ExtractValue ARM.ARM SoRegReg (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . soRegRegToBits

instance ExtractValue ARM.ARM LdstSoReg (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . ldstSoRegToBits



-- instance ExtractValue arch AddrModeImm12 (BVType 12) where
--   extractValue i = return $ MC.BVValue NR.knownNat (toInteger $ addrModeImm12ToBits i)
