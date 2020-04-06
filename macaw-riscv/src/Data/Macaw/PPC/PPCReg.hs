{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeFamilyDependencies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
-- | Defines the register types for PowerPC, along with some helpers
module Data.Macaw.PPC.PPCReg (
  PPCReg(..),
  linuxSystemCallPreservedRegisters,
  linuxCalleeSaveRegisters,
  ArchWidth(..),
  locToRegTH
  ) where

import           GHC.TypeLits

import           Data.Proxy ( Proxy(..) )
import qualified Data.Set as S
import           Language.Haskell.TH
import           Language.Haskell.TH.Syntax ( lift )
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types
import           Data.Parameterized.Classes
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TH.GADT as TH
import qualified Text.PrettyPrint.ANSI.Leijen as PP

import qualified Dismantle.PPC as D
import qualified SemMC.Architecture.PPC as PPC
import qualified SemMC.Architecture.PPC.Location as APPC

-- | The register type for PowerPC, parameterized by architecture to support
-- both PowerPC32 and PowerPC64

-- TODO: Refactor so that this takes the PPC variant as an argument
-- rather than the architecture (which is always @PPC.AnyPPC v@ for
-- some @v@).  This is likely to be disruptive.
data PPCReg arch tp where
  PPC_GP :: (w ~ MC.RegAddrWidth (PPCReg arch), 1 <= w) => D.GPR -> PPCReg arch (BVType w)
  PPC_FR :: D.VSReg -> PPCReg arch (BVType 128)
  PPC_IP :: (w ~ MC.RegAddrWidth (PPCReg arch), 1 <= w) => PPCReg arch (BVType w)
  PPC_LNK :: (w ~ MC.RegAddrWidth (PPCReg arch), 1 <= w) => PPCReg arch (BVType w)
  PPC_CTR :: (w ~ MC.RegAddrWidth (PPCReg arch), 1 <= w) => PPCReg arch (BVType w)
  PPC_CR :: PPCReg arch (BVType 32)
  PPC_XER :: (w ~ MC.RegAddrWidth (PPCReg arch), 1 <= w) => PPCReg arch (BVType w)
  PPC_FPSCR :: PPCReg arch (BVType 32)
  PPC_VSCR :: PPCReg arch (BVType 32)

deriving instance Eq (PPCReg arch tp)
deriving instance Ord (PPCReg arch tp)

instance Show (PPCReg arch tp) where
  show r =
    case r of
      PPC_GP (D.GPR gpr) -> 'r':show gpr
      PPC_FR (D.VSReg fr) -> 'f':show fr
      PPC_IP -> "ip"
      PPC_LNK -> "lnk"
      PPC_CTR -> "ctr"
      PPC_CR -> "cr"
      PPC_XER -> "xer"
      PPC_FPSCR -> "fpscr"
      PPC_VSCR -> "vscr"

instance ShowF (PPCReg arch) where
  showF = show

instance MC.PrettyF (PPCReg arch) where
  prettyF = PP.text . showF

$(return [])

instance TestEquality (PPCReg arch) where
  testEquality = $(TH.structuralTypeEquality [t| PPCReg |] [])

instance OrdF (PPCReg arch) where
  compareF = $(TH.structuralTypeOrd [t| PPCReg |] [])

-- | The set of registers preserved across Linux system calls is defined by the ABI.
--
-- Currently, we are only considering the non-volatile GPRs.  There are also a
-- set of non-volatile floating point registers.  I have to check on the vector
-- registers.
--
-- NOTE: As the name implies, this is Linux-specific.  Other ABIs will require
-- an analysis here.  That said, these are the register specs suggested by the
-- architecture manual, so they should be pretty consistent across ABIs.
linuxSystemCallPreservedRegisters :: (w ~ MC.RegAddrWidth (PPCReg ppc), 1 <= w)
                                  => proxy ppc
                                  -> S.Set (Some (PPCReg ppc))
linuxSystemCallPreservedRegisters _ =
  S.fromList [ Some (PPC_GP (D.GPR rnum)) | rnum <- [14..31] ]

linuxCalleeSaveRegisters :: (w ~ MC.RegAddrWidth (PPCReg ppc), 1 <= w)
                         => proxy ppc
                         -> S.Set (Some (PPCReg ppc))
linuxCalleeSaveRegisters _ =
  S.fromList [ Some (PPC_GP (D.GPR rnum)) | rnum <- [14..31] ]

type instance MC.RegAddrWidth (PPCReg (PPC.AnyPPC v)) = PPC.AddrWidth v
type instance MC.ArchReg (PPC.AnyPPC v) = PPCReg (PPC.AnyPPC v)

{-# DEPRECATED
      ArchWidth "Use 'SemMC.Architecture.AddrWidth' and 'SemMC.Architecture.addrWidth'."
#-}
class ArchWidth arch where
  pointerNatRepr :: proxy arch -> NatRepr (MC.RegAddrWidth (PPCReg arch))

instance PPC.KnownVariant v => ArchWidth (PPC.AnyPPC v) where
  pointerNatRepr _ = PPC.addrWidth (PPC.knownVariant @v)

instance (PPC.KnownVariant v, ppc ~ PPC.AnyPPC v) => HasRepr (PPCReg ppc) TypeRepr where
  typeRepr r =
    case r of
      PPC_GP {} -> BVTypeRepr (pointerNatRepr (Proxy @ppc))
      PPC_FR {} -> BVTypeRepr n128
      PPC_IP -> BVTypeRepr (pointerNatRepr (Proxy @ppc))
      PPC_LNK -> BVTypeRepr (pointerNatRepr (Proxy @ppc))
      PPC_CTR -> BVTypeRepr (pointerNatRepr (Proxy @ppc))
      PPC_CR -> BVTypeRepr n32
      PPC_XER -> BVTypeRepr (pointerNatRepr (Proxy @ppc))
      PPC_FPSCR -> BVTypeRepr n32
      PPC_VSCR -> BVTypeRepr n32

-- The MM.MemWidth constraint is always satisfiable, but sadly it has
-- to be included since GHC doesn't *know* it's always satisfiable :-\
instance ( PPC.KnownVariant v, MM.MemWidth (PPC.AddrWidth v)
         ) =>
         MC.RegisterInfo (PPCReg (PPC.AnyPPC v)) where
  archRegs = ppcRegs
  sp_reg = PPC_GP (D.GPR 1)
  ip_reg = PPC_IP
  syscall_num_reg = PPC_GP (D.GPR 0)
  syscallArgumentRegs = [ PPC_GP (D.GPR rnum) | rnum <- [3..10] ]

-- FIXME These should probably live somewhere else?

ppcRegs :: forall v
         . ( PPC.KnownVariant v )
        => [Some (PPCReg (PPC.AnyPPC v))]
ppcRegs = concat [ gprs
                 , sprs
                 , fprs
                 ]
  where
    sprs = [ Some PPC_IP, Some PPC_LNK, Some PPC_CTR, Some PPC_CR, Some PPC_XER, Some PPC_FPSCR, Some PPC_VSCR ]
    gprs = [ Some (PPC_GP (D.GPR rnum))
           | rnum <- [0..31]
           ]
    fprs = [ Some (PPC_FR (D.VSReg rnum))
           | rnum <- [0..63]
           ]

-- | Translate a location from the semmc semantics into a location suitable for
-- use in macaw
locToRegTH :: (PPC.KnownVariant v, ppc ~ PPC.AnyPPC v)
           => proxy ppc
           -> APPC.Location ppc ctp
           -> Q Exp
locToRegTH _ (APPC.LocGPR (D.GPR gpr)) = [| PPC_GP (D.GPR $(lift gpr)) |]
locToRegTH _ (APPC.LocVSR (D.VSReg vsr)) = [| PPC_FR (D.VSReg $(lift vsr)) |]
locToRegTH _  APPC.LocIP       = [| PPC_IP |]
locToRegTH _  APPC.LocLNK      = [| PPC_LNK |]
locToRegTH _  APPC.LocCTR      = [| PPC_CTR |]
locToRegTH _  APPC.LocCR       = [| PPC_CR |]
locToRegTH _  APPC.LocXER      = [| PPC_XER |]
locToRegTH _  APPC.LocFPSCR    = [| PPC_FPSCR |]
locToRegTH _  APPC.LocVSCR    = [| PPC_VSCR |]
locToRegTH _  _                = [| undefined |]
