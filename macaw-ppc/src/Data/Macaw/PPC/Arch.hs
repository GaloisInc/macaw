{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TypeFamilies          #-}
{-# LANGUAGE TypeOperators         #-}
module Data.Macaw.PPC.Arch (
  PPCTermStmt(..),
  rewriteTermStmt,
  PPCStmt(..),
  rewriteStmt,
  PPCPrimFn(..),
  rewritePrimFn,
  ppcPrimFnHasSideEffects,
  PPCArchConstraints
  ) where

import GHC.TypeLits

import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Data.Parameterized.TraversableFC as FC
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Macaw.CFG as MC
import           Data.Macaw.CFG.Rewriter ( Rewriter, rewriteValue, evalRewrittenArchFn )
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Types as MT

import qualified SemMC.Architecture.PPC32 as PPC32
import qualified SemMC.Architecture.PPC64 as PPC64

import Data.Macaw.PPC.PPCReg

data PPCTermStmt ids where
  -- | A representation of the PowerPC @sc@ instruction
  --
  -- That instruction technically takes an argument, but it must be zero so we
  -- don't preserve it.
  PPCSyscall :: PPCTermStmt ids
  -- | A non-syscall trap initiated by the @td@, @tw@, @tdi@, or @twi@ instructions
  PPCTrap :: PPCTermStmt ids

deriving instance Show (PPCTermStmt ids)

type instance MC.ArchTermStmt PPC64.PPC = PPCTermStmt
type instance MC.ArchTermStmt PPC32.PPC = PPCTermStmt

instance MC.PrettyF PPCTermStmt where
  prettyF ts =
    case ts of
      PPCSyscall -> PP.text "ppc_syscall"
      PPCTrap -> PP.text "ppc_trap"

rewriteTermStmt :: PPCTermStmt src -> Rewriter ppc s src tgt (PPCTermStmt tgt)
rewriteTermStmt s =
  case s of
    PPCSyscall -> pure PPCSyscall
    PPCTrap -> pure PPCTrap

-- | We currently have no PPC-specific statements.  Remove 'None' if we add some.
data PPCStmt ppc (v :: MT.Type -> *) where
  None :: PPCStmt ppc v

instance MC.PrettyF (PPCStmt ppc) where
  prettyF s =
    case s of
      None -> PP.text "None"

instance TF.FunctorF (PPCStmt ppc) where
  fmapF = TF.fmapFDefault

instance TF.FoldableF (PPCStmt ppc) where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF (PPCStmt ppc) where
  traverseF _go stmt =
    case stmt of
      None -> pure None

instance MC.IsArchStmt (PPCStmt ppc) where
  ppArchStmt _pp stmt =
    case stmt of
      None -> PP.text "none"

type instance MC.ArchStmt PPC64.PPC = PPCStmt PPC64.PPC
type instance MC.ArchStmt PPC32.PPC = PPCStmt PPC32.PPC

rewriteStmt :: PPCStmt ppc (MC.Value ppc src) -> Rewriter ppc s src tgt ()
rewriteStmt _ = return ()

data PPCPrimFn ppc f tp where
  IDiv :: proxy ppc
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> PPCPrimFn ppc f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))

instance MT.HasRepr (PPCPrimFn ppc (MC.Value ppc ids)) MT.TypeRepr where
  typeRepr f =
    case f of
      IDiv {} -> undefined

-- | Right now, none of the primitive functions has a side effect.  That will
-- probably change.
ppcPrimFnHasSideEffects :: PPCPrimFn ppc f tp -> Bool
ppcPrimFnHasSideEffects pf =
  case pf of
    IDiv {} -> False

rewritePrimFn :: (PPCArchConstraints ppc, MC.ArchFn ppc ~ PPCPrimFn ppc)
              => PPCPrimFn ppc (MC.Value ppc src) tp
              -> Rewriter ppc s src tgt (MC.Value ppc tgt tp)
rewritePrimFn f =
  case f of
    IDiv p lhs rhs -> do
      tgtFn <- IDiv p <$> rewriteValue lhs <*> rewriteValue rhs
      evalRewrittenArchFn tgtFn

ppPrimFn :: (Applicative m) => (forall u . f u -> m PP.Doc) -> PPCPrimFn ppc f tp -> m PP.Doc
ppPrimFn _pp f =
  case f of
    IDiv {} -> pure (PP.text "idiv")

instance MC.IsArchFn (PPCPrimFn ppc) where
  ppArchFn = ppPrimFn

instance FC.FunctorFC (PPCPrimFn ppc) where
  fmapFC = FC.fmapFCDefault

instance FC.FoldableFC (PPCPrimFn ppc) where
  foldMapFC = FC.foldMapFCDefault

instance FC.TraversableFC (PPCPrimFn ppc) where
  traverseFC go f =
    case f of
      IDiv p lhs rhs -> IDiv p <$> go lhs <*> go rhs

type instance MC.ArchFn PPC64.PPC = PPCPrimFn PPC64.PPC
type instance MC.ArchFn PPC32.PPC = PPCPrimFn PPC32.PPC

type PPCArchConstraints ppc = ( MC.ArchReg ppc ~ PPCReg ppc
                              , MC.ArchFn ppc ~ PPCPrimFn ppc
                              , MC.ArchStmt ppc ~ PPCStmt ppc
                              , MC.ArchTermStmt ppc ~ PPCTermStmt
                              , ArchWidth ppc
                              , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg ppc))
                              , 1 <= MC.RegAddrWidth (PPCReg ppc)
                              , KnownNat (MC.RegAddrWidth (PPCReg ppc))
                              , MC.ArchConstraints ppc
                              )
