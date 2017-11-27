{-# LANGUAGE ConstraintKinds       #-}
{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE TemplateHaskell       #-}
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
  PPCArchConstraints,
  specialSemanticsCases
  ) where

import           GHC.TypeLits

import           Language.Haskell.TH
import qualified Text.PrettyPrint.ANSI.Leijen as PP
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

import           Data.Macaw.PPC.PPCReg

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

data PPCStmt ppc (v :: MT.Type -> *) where
  Attn :: PPCStmt ppc v
  Sync :: PPCStmt ppc v
  Isync :: PPCStmt ppc v

instance MC.PrettyF (PPCStmt ppc) where
  prettyF s =
    case s of
      Attn -> PP.text "ppc_attn"
      Sync -> PP.text "ppc_sync"
      Isync -> PP.text "ppc_isync"

instance TF.FunctorF (PPCStmt ppc) where
  fmapF = TF.fmapFDefault

instance TF.FoldableF (PPCStmt ppc) where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF (PPCStmt ppc) where
  traverseF _go stmt =
    case stmt of
      Attn -> pure Attn
      Sync -> pure Sync
      Isync -> pure Isync

instance MC.IsArchStmt (PPCStmt ppc) where
  ppArchStmt _pp stmt =
    case stmt of
      Attn -> PP.text "ppc_attn"
      Sync -> PP.text "ppc_sync"
      Isync -> PP.text "ppc_isync"

type instance MC.ArchStmt PPC64.PPC = PPCStmt PPC64.PPC
type instance MC.ArchStmt PPC32.PPC = PPCStmt PPC32.PPC

rewriteStmt :: (MC.ArchStmt ppc ~ PPCStmt ppc) => PPCStmt ppc (MC.Value ppc src) -> Rewriter ppc s src tgt ()
rewriteStmt s = do
  s' <- TF.traverseF rewriteValue s
  appendRewrittenArchStmt s'

data PPCPrimFn ppc f tp where
  UDiv :: NR.NatRepr (MC.RegAddrWidth (MC.ArchReg ppc))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> PPCPrimFn ppc f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
  SDiv :: NR.NatRepr (MC.RegAddrWidth (MC.ArchReg ppc))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))
       -> PPCPrimFn ppc f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ppc)))

instance (1 <= MC.RegAddrWidth (MC.ArchReg ppc)) => MT.HasRepr (PPCPrimFn ppc (MC.Value ppc ids)) MT.TypeRepr where
  typeRepr f =
    case f of
      UDiv rep _ _ -> MT.BVTypeRepr rep
      SDiv rep _ _ -> MT.BVTypeRepr rep

-- | Right now, none of the primitive functions has a side effect.  That will
-- probably change.
ppcPrimFnHasSideEffects :: PPCPrimFn ppc f tp -> Bool
ppcPrimFnHasSideEffects pf =
  case pf of
    UDiv {} -> False
    SDiv {} -> False

rewritePrimFn :: (PPCArchConstraints ppc, MC.ArchFn ppc ~ PPCPrimFn ppc)
              => PPCPrimFn ppc (MC.Value ppc src) tp
              -> Rewriter ppc s src tgt (MC.Value ppc tgt tp)
rewritePrimFn f =
  case f of
    UDiv rep lhs rhs -> do
      tgtFn <- UDiv rep <$> rewriteValue lhs <*> rewriteValue rhs
      evalRewrittenArchFn tgtFn
    SDiv rep lhs rhs -> do
      tgtFn <- SDiv rep <$> rewriteValue lhs <*> rewriteValue rhs
      evalRewrittenArchFn tgtFn

ppPrimFn :: (Applicative m) => (forall u . f u -> m PP.Doc) -> PPCPrimFn ppc f tp -> m PP.Doc
ppPrimFn pp f =
  case f of
    UDiv _ lhs rhs -> (\lhs' rhs' -> PP.text "ppc_udiv " PP.<> lhs' PP.<> PP.text " " PP.<> rhs') <$> pp lhs <*> pp rhs
    SDiv _ lhs rhs -> (\lhs' rhs' -> PP.text "ppc_sdiv " PP.<> lhs' PP.<> PP.text " " PP.<> rhs') <$> pp lhs <*> pp rhs

instance MC.IsArchFn (PPCPrimFn ppc) where
  ppArchFn = ppPrimFn

instance FC.FunctorFC (PPCPrimFn ppc) where
  fmapFC = FC.fmapFCDefault

instance FC.FoldableFC (PPCPrimFn ppc) where
  foldMapFC = FC.foldMapFCDefault

instance FC.TraversableFC (PPCPrimFn ppc) where
  traverseFC go f =
    case f of
      UDiv rep lhs rhs -> UDiv rep <$> go lhs <*> go rhs
      SDiv rep lhs rhs -> SDiv rep <$> go lhs <*> go rhs

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

-- | Manually-provided semantics for instructions whose full semantics cannot be
-- expressed in our semantics format.
--
-- This includes instructions with special side effects that we don't have a way
-- to talk about in the semantics; especially useful for architecture-specific
-- terminator statements.
specialSemanticsCases :: [MatchQ]
specialSemanticsCases =
  [ match (conP 'D.SC []) (normalB [| Just (finishWithTerminator (MC.ArchTermStmt PPCSyscall)) |]) []
  , match (conP 'D.TRAP []) (normalB [| Just (finishWithTerminator (MC.ArchTermStmt PPCTrap)) |]) []
  , match (conP 'D.ATTN []) (normalB [| Just (addStmt (MC.ExecArchStmt Attn)) |]) []
  , match (conP 'D.SYNC []) (normalB [| Just (addStmt (MC.ExecArchStmt Sync)) |]) []
  , match (conP 'D.ISYNC []) (normalB [| Just (addStmt (MC.ExecArchStmt Isync)) |]) []
  ]
