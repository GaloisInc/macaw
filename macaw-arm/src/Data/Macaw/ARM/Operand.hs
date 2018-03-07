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
import           Data.Word ( Word16, Word8 )
import qualified Dismantle.ARM.Operands as A32Operand
import qualified Dismantle.Thumb.Operands as T32Operand
import qualified SemMC.ARM as ARM


instance ExtractValue ARM.ARM A32Operand.GPR (BVType 32) where
  extractValue r = G.getRegValue (Reg.ARM_GP $ A32Operand.unGPR r)


instance ToRegister A32Operand.GPR Reg.ARMReg (BVType 32) where
  toRegister = Reg.ARM_GP . A32Operand.unGPR


instance ExtractValue ARM.ARM (Maybe A32Operand.GPR) (BVType 32) where
  extractValue mgpr =
    case mgpr of
      Just r -> extractValue r
      Nothing -> return $ MC.BVValue NR.knownNat 0

instance ExtractValue ARM.ARM A32Operand.Pred (BVType 4) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . A32Operand.predToBits

instance ExtractValue ARM.ARM A32Operand.SBit (BVType 1) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . A32Operand.sBitToBits

instance ExtractValue ARM.ARM A32Operand.Imm5 (BVType 5) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . A32Operand.imm5ToBits

instance ExtractValue ARM.ARM A32Operand.BranchTarget (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . A32Operand.branchTargetToBits

instance ExtractValue ARM.ARM A32Operand.BranchExecuteTarget (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . A32Operand.branchExecuteTargetToBits

instance ExtractValue ARM.ARM A32Operand.SoRegImm (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . A32Operand.soRegImmToBits

instance ExtractValue ARM.ARM A32Operand.SoRegReg (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . A32Operand.soRegRegToBits

instance ExtractValue ARM.ARM A32Operand.LdstSoReg (BVType 32) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . A32Operand.ldstSoRegToBits

instance ExtractValue arch Word16 (BVType 16) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger

instance ExtractValue ARM.ARM Word8 (BVType 8) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger



-- instance ExtractValue arch AddrModeImm12 (BVType 12) where
--   extractValue i = return $ MC.BVValue NR.knownNat (toInteger $ addrModeImm12ToBits i)

-- ----------------------------------------------------------------------

instance ExtractValue ARM.ARM T32Operand.GPR (BVType 32) where
  extractValue r = G.getRegValue (Reg.ARM_GP $ T32Operand.unGPR r)


instance ToRegister T32Operand.GPR Reg.ARMReg (BVType 32) where
  toRegister = Reg.ARM_GP . T32Operand.unGPR


instance ExtractValue ARM.ARM (Maybe T32Operand.GPR) (BVType 32) where
  extractValue mgpr =
    case mgpr of
      Just r -> extractValue r
      Nothing -> return $ MC.BVValue NR.knownNat 0

instance ExtractValue ARM.ARM T32Operand.Opcode (BVType 3) where
  extractValue = return . MC.BVValue NR.knownNat . toInteger . T32Operand.opcodeToBits

instance ExtractValue ARM.ARM T32Operand.LowGPR (BVType 32) where
  extractValue r = G.getRegValue (Reg.ARM_GP $ T32Operand.unLowGPR r)

instance ToRegister T32Operand.LowGPR Reg.ARMReg (BVType 32) where
  toRegister = Reg.ARM_GP . T32Operand.unLowGPR
