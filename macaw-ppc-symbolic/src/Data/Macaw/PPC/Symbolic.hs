{-# LANGUAGE AllowAmbiguousTypes #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}
module Data.Macaw.PPC.Symbolic (
  ppc64MacawSymbolicFns,
  ppc64MacawEvalFn,
  ppc32MacawSymbolicFns,
  ppc32MacawEvalFn,
  F.SymFuns,
  F.newSymFuns,
  getReg,
  -- * Register names
  IP,
  LNK,
  CTR,
  XER,
  CR,
  FPSCR,
  VSCR,
  GP,
  FR
  ) where

import           GHC.TypeLits

import           Control.Lens ( (^.) )
import qualified Data.Functor.Identity as I
import qualified Data.Parameterized.Context as Ctx
import qualified Data.Parameterized.TraversableFC as FC
import qualified Dismantle.PPC as D
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.Solver.Symbol as C
import qualified Lang.Crucible.Solver.Interface as C

import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Data.Macaw.Symbolic as MS
import qualified Data.Macaw.Symbolic.PersistentState as MS
import qualified Data.Macaw.PPC as MP

import qualified Data.Macaw.PPC.Symbolic.AtomWrapper as A
import qualified Data.Macaw.PPC.Symbolic.Functions as F
import qualified Data.Macaw.PPC.Symbolic.Repeat as R

ppc64MacawSymbolicFns :: MS.MacawSymbolicArchFunctions MP.PPC64
ppc64MacawSymbolicFns =
  MS.MacawSymbolicArchFunctions
  { MS.crucGenArchConstraints = \x -> x
  , MS.crucGenArchRegName = ppcRegName
  , MS.crucGenRegAssignment = ppcRegAssignment
  , MS.crucGenArchFn = ppcGenFn
  , MS.crucGenArchStmt = ppcGenStmt
  , MS.crucGenArchTermStmt = ppcGenTermStmt
  }

ppc32MacawSymbolicFns :: MS.MacawSymbolicArchFunctions MP.PPC32
ppc32MacawSymbolicFns =
  MS.MacawSymbolicArchFunctions
  { MS.crucGenArchConstraints = \x -> x
  , MS.crucGenArchRegName = ppcRegName
  , MS.crucGenRegAssignment = ppcRegAssignment
  , MS.crucGenArchFn = ppcGenFn
  , MS.crucGenArchStmt = ppcGenStmt
  , MS.crucGenArchTermStmt = ppcGenTermStmt
  }

type RegSize ppc = MC.RegAddrWidth (MP.PPCReg ppc)
type RegContext ppc
  =     (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize ppc)) -- IP
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize ppc)) -- LNK
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize ppc)) -- CTR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType (RegSize ppc)) -- XER
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)            -- CR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)            -- FPSCR
  C.<+> (Ctx.EmptyCtx Ctx.::> MT.BVType 32)            -- VSCR
  C.<+> R.CtxRepeat 32 (MT.BVType (RegSize ppc))       -- GPRs
  C.<+> R.CtxRepeat 64 (MT.BVType 128)                 -- VSRs

type instance MS.ArchRegContext MP.PPC64 = RegContext MP.PPC64
type instance MS.ArchRegContext MP.PPC32 = RegContext MP.PPC32

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

getReg :: forall n t f ppc . (Ctx.Idx n (MS.ArchRegContext ppc) t) => RegAssign ppc f -> f t
getReg = (^. (Ctx.field @n))

ppc64MacawEvalFn :: (C.IsSymInterface sym)
                 => F.SymFuns MP.PPC64 sym
                 -> MS.MacawArchEvalFn sym MP.PPC64
ppc64MacawEvalFn fs = \(PPCPrimFn x) s -> F.semantics fs x s

ppc32MacawEvalFn :: (C.IsSymInterface sym)
                 => F.SymFuns MP.PPC32 sym
                 -> MS.MacawArchEvalFn sym MP.PPC32
ppc32MacawEvalFn fs = \(PPCPrimFn x) s -> F.semantics fs x s

ppcRegName :: MP.PPCReg ppc tp -> C.SolverSymbol
ppcRegName r = C.systemSymbol ("!" ++ show (MC.prettyF r))

ppcRegAssignment :: forall ppc
                  . (1 <= RegSize ppc)
                 => Ctx.Assignment (MP.PPCReg ppc) (RegContext ppc)
ppcRegAssignment =
  (Ctx.Empty Ctx.:> MP.PPC_IP
            Ctx.:> MP.PPC_LNK
            Ctx.:> MP.PPC_CTR
            Ctx.:> MP.PPC_XER
            Ctx.:> MP.PPC_CR
            Ctx.:> MP.PPC_FPSCR
            Ctx.:> MP.PPC_VSCR)
  Ctx.<++> (R.repeatAssign (MP.PPC_GP . D.GPR . fromIntegral) :: Ctx.Assignment (MP.PPCReg ppc) (R.CtxRepeat 32 (MT.BVType (RegSize ppc))))
  Ctx.<++> (R.repeatAssign (MP.PPC_FR . D.VSReg . fromIntegral) :: Ctx.Assignment (MP.PPCReg ppc) (R.CtxRepeat 64 (MT.BVType 128)))

ppcGenFn :: forall ids s tp ppc
          . (MS.MacawArchStmtExtension ppc ~ PPCStmtExtension ppc)
         => MP.PPCPrimFn ppc (MC.Value ppc ids) tp
         -> MS.CrucGen ppc ids s (C.Atom s (MS.ToCrucibleType tp))
ppcGenFn fn = do
  let f :: MC.Value ppc ids a -> MS.CrucGen ppc ids s (A.AtomWrapper (C.Atom s) a)
      f x = A.AtomWrapper <$> MS.valueToCrucible x
  r <- FC.traverseFC f fn
  MS.evalArchStmt (PPCPrimFn r)

ppcGenStmt :: MP.PPCStmt ppc (MC.Value ppc ids)
           -> MS.CrucGen ppc ids s ()
ppcGenStmt _s = error "ppcGenStmt is not yet implemented"

ppcGenTermStmt :: MP.PPCTermStmt ids
               -> MC.RegState (MP.PPCReg ppc) (MC.Value ppc ids)
               -> MS.CrucGen ppc ids s ()
ppcGenTermStmt _ts _rs = error "ppcGenTermStmt is not yet implemented"

data PPCStmtExtension ppc (f :: C.CrucibleType -> *) (ctp :: C.CrucibleType) where
  PPCPrimFn :: MP.PPCPrimFn ppc (A.AtomWrapper f) t
            -> PPCStmtExtension ppc f (MS.ToCrucibleType t)

instance FC.FunctorFC (PPCStmtExtension ppc) where
  fmapFC f (PPCPrimFn x) = PPCPrimFn (FC.fmapFC (A.liftAtomMap f) x)

instance FC.FoldableFC (PPCStmtExtension ppc) where
  foldMapFC f (PPCPrimFn x) = FC.foldMapFC (A.liftAtomIn f) x

instance FC.TraversableFC (PPCStmtExtension ppc) where
  traverseFC f (PPCPrimFn x) = PPCPrimFn <$> FC.traverseFC (A.liftAtomTrav f) x

instance (1 <= MC.RegAddrWidth (MC.ArchReg ppc)) => C.TypeApp (PPCStmtExtension ppc) where
  appType (PPCPrimFn x) = MS.typeToCrucible (MT.typeRepr x)

instance C.PrettyApp (PPCStmtExtension ppc) where
  ppApp ppSub (PPCPrimFn x) =
    I.runIdentity (MC.ppArchFn (I.Identity . A.liftAtomIn ppSub) x)

type instance MS.MacawArchStmtExtension MP.PPC64 = PPCStmtExtension MP.PPC64
type instance MS.MacawArchStmtExtension MP.PPC32 = PPCStmtExtension MP.PPC32

