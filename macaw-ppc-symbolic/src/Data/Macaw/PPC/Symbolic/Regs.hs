{-|
Copyright        : (c) Galois, Inc 2024
Maintainer       : Langston Barrett <langston@galois.com>

PPC registers.

This module is meant to be imported qualified, as it exports many terse names.
-}

{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Data.Macaw.PPC.Symbolic.Regs
  ( RegContext
  , PPCSymbolicException(..)
  , ppcRegName
  , ppcRegAssignment
  , ppcRegStructType
  , getReg
  , regIndexMap
  , lookupReg
  , updateReg
  , IP, LNK, CTR, XER, CR, FPSCR, VSCR, GP, FR
  , ip
  ) where

import           Control.Lens ( (^.), (%~), (&) )
import qualified Control.Monad.Catch as X
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.Map as MapF
import           Data.Parameterized.Some ( Some(..) )
import qualified Data.Parameterized.TraversableFC as FC
import           Data.Typeable ( Typeable )
import qualified Dismantle.PPC as D
import           GHC.TypeLits
import qualified Lang.Crucible.LLVM.MemModel as MM
import qualified Lang.Crucible.Types as C
import qualified What4.Interface as C
import qualified What4.Symbol as C

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.Backend as MSB
import qualified Data.Macaw.PPC as MP

import qualified Data.Macaw.PPC.Symbolic.Repeat as R

type RegSize v = MC.RegAddrWidth (MP.PPCReg v)
type RegContext v
  =     (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- IP
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- LNK
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- CTR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize v)) -- XER
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- CR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- FPSCR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)          -- VSCR
  C.<+> R.CtxRepeat 32 (MT.BVType (RegSize v))       -- GPRs
  C.<+> R.CtxRepeat 64 (MT.BVType 128)               -- VSRs

type instance MS.ArchRegContext (MP.AnyPPC v) = RegContext v

ppcRegAssignment :: forall v
                  . ( MP.KnownVariant v )
                 => Ctx.Assignment (MP.PPCReg v) (RegContext v)
ppcRegAssignment =
  (Ctx.Empty Ctx.:> MP.PPC_IP
            Ctx.:> MP.PPC_LNK
            Ctx.:> MP.PPC_CTR
            Ctx.:> MP.PPC_XER
            Ctx.:> MP.PPC_CR
            Ctx.:> MP.PPC_FPSCR
            Ctx.:> MP.PPC_VSCR)
  Ctx.<++> (R.repeatAssign (MP.PPC_GP . D.GPR . fromIntegral) :: Ctx.Assignment (MP.PPCReg v) (R.CtxRepeat 32 (MT.BVType (RegSize v))))
  Ctx.<++> (R.repeatAssign (MP.PPC_FR . D.VSReg . fromIntegral) :: Ctx.Assignment (MP.PPCReg v) (R.CtxRepeat 64 (MT.BVType 128)))

type RegAssign ppc f = Ctx.Assignment f (MS.ArchRegContext ppc)

type IP = 0
type LNK = 1
type CTR = 2
type XER = 3
type CR = 4
type FPSCR = 5
type VSCR = 6
type GP n = 7 + n
type FR n = 39 + n

ip :: Ctx.Index (MS.MacawCrucibleRegTypes (MP.AnyPPC v)) (MM.LLVMPointerType (RegSize v))
ip = Ctx.natIndex @IP

getReg :: forall n t f ppc . (Ctx.Idx n (MS.ArchRegContext ppc) t) => RegAssign ppc f -> f t
getReg = (^. (Ctx.field @n))

ppcRegName :: MP.PPCReg v tp -> C.SolverSymbol
ppcRegName r = C.systemSymbol ("r!" ++ show (MC.prettyF r))

ppcRegStructType :: forall v
                  . ( MP.KnownVariant v )
                 => C.TypeRepr (MS.ArchRegStruct (MP.AnyPPC v))
ppcRegStructType =
  C.StructRepr (MS.typeCtxToCrucible $ FC.fmapFC MT.typeRepr ppcRegAssignment)

data PPCSymbolicException v = MissingRegisterInState (Some (MP.PPCReg v))

deriving instance Show (PPCSymbolicException v)

instance Typeable v => X.Exception (PPCSymbolicException v)

regIndexMap :: forall v
             . MP.KnownVariant v
            => MSB.RegIndexMap (MP.AnyPPC v)
regIndexMap = MSB.mkRegIndexMap assgn sz
  where
    assgn = ppcRegAssignment @v
    sz = Ctx.size (MS.typeCtxToCrucible (FC.fmapFC MT.typeRepr assgn))

lookupReg :: forall v ppc m f tp
           . (MP.KnownVariant v,
              ppc ~ MP.AnyPPC v,
              X.MonadThrow m)
          => MP.PPCReg v tp
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc)
          -> m (f (MS.ToCrucibleType tp))
lookupReg r asgn =
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn Ctx.! MSB.crucibleIndex pair)

updateReg :: forall v ppc m f tp
           . (MP.KnownVariant v,
               ppc ~ MP.AnyPPC v,
               X.MonadThrow m)
          => MP.PPCReg v tp
          -> (f (MS.ToCrucibleType tp) -> f (MS.ToCrucibleType tp))
          -> Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc)
          -> m (Ctx.Assignment f (MS.MacawCrucibleRegTypes ppc))
updateReg r upd asgn = do
  case MapF.lookup r regIndexMap of
    Nothing -> X.throwM (MissingRegisterInState (Some r))
    Just pair -> return (asgn & MapF.ixF (MSB.crucibleIndex pair) %~ upd)
