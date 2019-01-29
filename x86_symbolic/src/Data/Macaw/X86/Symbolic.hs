{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE PolyKinds #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE UndecidableInstances #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE AllowAmbiguousTypes #-}
{-# OPTIONS_GHC -fno-warn-orphans #-}
module Data.Macaw.X86.Symbolic
  ( x86_64MacawSymbolicFns
  , x86_64MacawEvalFn
  , SymFuns(..), newSymFuns

  , lookupX86Reg
  , updateX86Reg
  , freshX86Reg

  , RegAssign
  , getReg
  , IP, GP, Flag, X87Status, X87Top, X87Tag, FPReg, YMM
  ) where

import           Control.Lens ((^.),(%~),(&))
import           Control.Monad ( void )
import           Control.Monad.IO.Class ( liftIO )
import           Data.Functor.Identity (Identity(..))
import           Data.Kind
import           Data.Parameterized.Context as Ctx
import           Data.Parameterized.Map as MapF
import           Data.Parameterized.TraversableF
import           Data.Parameterized.TraversableFC
import           GHC.TypeLits

import qualified Data.Macaw.CFG as M
import           Data.Macaw.Symbolic
import           Data.Macaw.Symbolic.Backend
import qualified Data.Macaw.Types as M
import qualified Data.Macaw.X86 as M
import qualified Data.Macaw.X86.X86Reg as M
import           Data.Macaw.X86.Crucible
import qualified Flexdis86.Register as F

import qualified What4.Interface as WI
import qualified What4.InterpretedFloatingPoint as WIF
import qualified What4.Symbol as C

import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.CFG.Extension as C
import qualified Lang.Crucible.CFG.Reg as C
import qualified Lang.Crucible.Simulator as C
import qualified Lang.Crucible.Types as C
import qualified Lang.Crucible.LLVM.MemModel as MM

------------------------------------------------------------------------
-- Utilities for generating a type-level context with repeated elements.

type family CtxRepeat (n :: Nat) (c :: k) :: Ctx k where
  CtxRepeat  0 c = EmptyCtx
  CtxRepeat  n c = CtxRepeat  (n-1) c ::> c

class RepeatAssign (tp :: k) (ctx :: Ctx k) where
  repeatAssign :: (Int -> f tp) -> Assignment f ctx

instance RepeatAssign tp EmptyCtx where
  repeatAssign _ = Empty

instance RepeatAssign tp ctx => RepeatAssign tp (ctx ::> tp) where
  repeatAssign f =
    let r = repeatAssign f
     in r :> f (sizeInt (Ctx.size r))

------------------------------------------------------------------------
-- X86 Registers

type instance ArchRegContext M.X86_64
   =   (EmptyCtx ::> M.BVType 64)   -- IP
   <+> CtxRepeat 16 (M.BVType 64)   -- GP regs
   <+> CtxRepeat 9  M.BoolType      -- Flags
   <+> CtxRepeat 12  M.BoolType     -- X87 Status regs (x87 status word)
   <+> (EmptyCtx ::> M.BVType 3)    -- X87 top of the stack (x87 status word)
   <+> CtxRepeat 8 (M.BVType 2)     -- X87 tags
   <+> CtxRepeat 8 (M.BVType 80)    -- FP regs
   <+> CtxRepeat 16 (M.BVType 256)  -- YMM regs

type RegAssign f = Assignment f (ArchRegContext M.X86_64)

type IP          = 0        -- 1
type GP n        = 1 + n    -- 16
type Flag n      = 17 + n   -- 9
type X87Status n = 26 + n   -- 12
type X87Top      = 38       -- 1
type X87Tag n    = 39 + n   -- 8
type FPReg n     = 47 + n   -- 8
type YMM n       = 55 + n   -- 16

getReg ::
  forall n t f. (Idx n (ArchRegContext M.X86_64) t) => RegAssign f -> f t
getReg x = x ^. (field @n)

x86RegName' :: M.X86Reg tp -> String
x86RegName' M.X86_IP     = "ip"
x86RegName' (M.X86_GP r) = show r
x86RegName' (M.X86_FlagReg r) = show r
x86RegName' (M.X87_StatusReg r) = show r
x86RegName' M.X87_TopReg = "x87Top"
x86RegName' (M.X87_TagReg r) = "x87Tag" ++ show r
x86RegName' (M.X87_FPUReg r) = show r
x86RegName' (M.X86_YMMReg r) = show r

x86RegName :: M.X86Reg tp -> C.SolverSymbol
x86RegName r = C.systemSymbol $ "r!" ++ x86RegName' r

gpReg :: Int -> M.X86Reg (M.BVType 64)
gpReg = M.X86_GP . F.Reg64 . fromIntegral

-- | The x86 flag registers that are directly supported by Macw.
flagRegs :: Assignment M.X86Reg (CtxRepeat 9 M.BoolType)
flagRegs =
  Empty :> M.CF :> M.PF :> M.AF :> M.ZF :> M.SF :> M.TF :> M.IF :> M.DF :> M.OF

x87_statusRegs :: Assignment M.X86Reg (CtxRepeat 12 M.BoolType)
x87_statusRegs =
     (repeatAssign (M.X87_StatusReg . fromIntegral)
        :: Assignment M.X86Reg (CtxRepeat 11 M.BoolType))
  :> M.X87_StatusReg 14

-- | This contains an assignment that stores the register associated with each index in the
-- X86 register structure.
x86RegAssignment :: Assignment M.X86Reg (ArchRegContext M.X86_64)
x86RegAssignment =
  Empty :> M.X86_IP
  <++> (repeatAssign gpReg :: Assignment M.X86Reg (CtxRepeat 16 (M.BVType 64)))
  <++> flagRegs
  <++> x87_statusRegs
  <++> (Empty :> M.X87_TopReg)
  <++> (repeatAssign (M.X87_TagReg . fromIntegral)    :: Assignment M.X86Reg (CtxRepeat  8 (M.BVType 2)))
  <++> (repeatAssign (M.X87_FPUReg . F.mmxReg . fromIntegral) :: Assignment M.X86Reg (CtxRepeat  8 (M.BVType 80)))
  <++> (repeatAssign (M.X86_YMMReg . F.ymmReg . fromIntegral) :: Assignment M.X86Reg (CtxRepeat 16 (M.BVType 256)))


regIndexMap :: RegIndexMap M.X86_64
regIndexMap = mkRegIndexMap x86RegAssignment
            $ Ctx.size $ crucArchRegTypes x86_64MacawSymbolicFns


{- | Lookup a Macaw register in a Crucible assignemnt.
This function returns "Nothing" if the input register is not represented
in the assignment.  This means that either the input register is malformed,
or we haven't modelled this register for some reason. -}
lookupX86Reg ::
  M.X86Reg t                                    {- ^ Lookup this register -} ->
  Assignment f (MacawCrucibleRegTypes M.X86_64) {- ^ Assignment -} ->
  Maybe (f (ToCrucibleType t))  {- ^ The value of the register -}
lookupX86Reg r asgn =
  do pair <- MapF.lookup r regIndexMap
     return (asgn Ctx.! crucibleIndex pair)

updateX86Reg ::
  M.X86Reg t ->
  (f (ToCrucibleType t) -> f (ToCrucibleType t)) ->
  Assignment f (MacawCrucibleRegTypes M.X86_64) {- ^Update this assignment -} ->
  Maybe (Assignment f (MacawCrucibleRegTypes M.X86_64))
updateX86Reg r upd asgn =
  do pair <- MapF.lookup r regIndexMap
     return (asgn & ixF (crucibleIndex pair) %~ upd)
     -- return (adjust upd (crucibleIndex pair) asgn)

freshX86Reg :: C.IsSymInterface sym =>
  sym -> M.X86Reg t -> IO (C.RegValue' sym (ToCrucibleType t))
freshX86Reg sym r =
  C.RV <$> freshValue sym (show r) (Just (C.knownNat @64))  (M.typeRepr r)

freshValue ::
  (C.IsSymInterface sym, 1 <= ptrW) =>
  sym ->
  String {- ^ Name for fresh value -} ->
  Maybe (C.NatRepr ptrW) {- ^ Width of pointers; if nothing, allocate as bits -} ->
  M.TypeRepr tp {- ^ Type of value -} ->
  IO (C.RegValue sym (ToCrucibleType tp))
freshValue sym str w ty =
  case ty of
    M.BVTypeRepr y ->
      case testEquality y =<< w of

        Just Refl ->
          do nm_base <- symName (str ++ "_base")
             nm_off  <- symName (str ++ "_off")
             base    <- WI.freshConstant sym nm_base C.BaseNatRepr
             offs    <- WI.freshConstant sym nm_off (C.BaseBVRepr y)
             return (MM.LLVMPointer base offs)

        Nothing ->
          do nm   <- symName str
             base <- WI.natLit sym 0
             offs <- WI.freshConstant sym nm (C.BaseBVRepr y)
             return (MM.LLVMPointer base offs)

    M.FloatTypeRepr fi -> do
      nm <- symName str
      WIF.freshFloatConstant sym nm $ floatInfoToCrucible fi

    M.BoolTypeRepr ->
      do nm <- symName str
         WI.freshConstant sym nm C.BaseBoolRepr

    M.TupleTypeRepr {} -> crash [ "Unexpected symbolic tuple:", show str ]

  where
  symName x =
    case C.userSymbol ("macaw_" ++ x) of
      Left err -> crash [ "Invalid symbol name:", show x, show err ]
      Right a -> return a

  crash xs =
    case xs of
      [] -> crash ["(unknown)"]
      y : ys -> fail $ unlines $ ("[freshX86Reg] " ++ y)
                               : [ "*** " ++ z | z <- ys ]


------------------------------------------------------------------------




------------------------------------------------------------------------
-- Other X86 specific


-- | We currently make a type like this, we could instead a generic
-- X86PrimFn function
data X86StmtExtension (f :: C.CrucibleType -> Type) (ctp :: C.CrucibleType) where
  -- | To reduce clutter, but potentially increase clutter, we just make every
  -- Macaw X86PrimFn a Macaw-Crucible statement extension.
  X86PrimFn :: !(M.X86PrimFn (AtomWrapper f) t) ->
                                        X86StmtExtension f (ToCrucibleType t)
  X86PrimStmt :: !(M.X86Stmt (AtomWrapper f))
              -> X86StmtExtension f C.UnitType
  X86PrimTerm :: !(M.X86TermStmt ids) -> X86StmtExtension f C.UnitType


instance C.PrettyApp X86StmtExtension where
  ppApp ppSub (X86PrimFn x) = d
    where Identity d = M.ppArchFn (Identity . liftAtomIn ppSub) x
  ppApp ppSub (X86PrimStmt stmt) = M.ppArchStmt (liftAtomIn ppSub) stmt
  ppApp _ppSub (X86PrimTerm term) = M.prettyF term

instance C.TypeApp X86StmtExtension where
  appType (X86PrimFn x) = typeToCrucible (M.typeRepr x)
  appType (X86PrimStmt _) = C.UnitRepr
  appType (X86PrimTerm _) = C.UnitRepr

instance FunctorFC X86StmtExtension where
  fmapFC f (X86PrimFn x) = X86PrimFn (fmapFC (liftAtomMap f) x)
  fmapFC f (X86PrimStmt stmt) = X86PrimStmt (fmapF (liftAtomMap f) stmt)
  fmapFC _f (X86PrimTerm term) = X86PrimTerm term

instance FoldableFC X86StmtExtension where
  foldMapFC f (X86PrimFn x) = foldMapFC (liftAtomIn f) x
  foldMapFC f (X86PrimStmt stmt) = foldMapF (liftAtomIn f) stmt
  -- There are no contents in terminator statements for now
  foldMapFC _f (X86PrimTerm _term) = mempty

instance TraversableFC X86StmtExtension where
  traverseFC f (X86PrimFn x) = X86PrimFn <$> traverseFC (liftAtomTrav f) x
  traverseFC f (X86PrimStmt stmt) = X86PrimStmt <$> traverseF (liftAtomTrav f) stmt
  traverseFC _f (X86PrimTerm term) = pure (X86PrimTerm term)

type instance MacawArchStmtExtension M.X86_64 = X86StmtExtension


crucGenX86Fn :: forall ids h s tp. M.X86PrimFn (M.Value M.X86_64 ids) tp
             -> CrucGen M.X86_64 ids h s (C.Atom s (ToCrucibleType tp))
crucGenX86Fn fn = do
  let f ::  M.Value arch ids a -> CrucGen arch ids h s (AtomWrapper (C.Atom s) a)
      f x = AtomWrapper <$> valueToCrucible x
  r <- traverseFC f fn
  evalArchStmt (X86PrimFn r)


crucGenX86Stmt :: forall ids h s
                . M.X86Stmt (M.Value M.X86_64 ids)
               -> CrucGen M.X86_64 ids h s ()
crucGenX86Stmt stmt = do
  let f :: M.Value M.X86_64 ids a -> CrucGen M.X86_64 ids h s (AtomWrapper (C.Atom s) a)
      f x = AtomWrapper <$> valueToCrucible x
  stmt' <- traverseF f stmt
  void (evalArchStmt (X86PrimStmt stmt'))

crucGenX86TermStmt :: M.X86TermStmt ids
                   -> M.RegState M.X86Reg (M.Value M.X86_64 ids)
                   -> CrucGen M.X86_64 ids h s ()
crucGenX86TermStmt tstmt _regs =
  void (evalArchStmt (X86PrimTerm tstmt))

-- | X86_64 specific functions for translation Macaw into Crucible.
x86_64MacawSymbolicFns :: MacawSymbolicArchFunctions M.X86_64
x86_64MacawSymbolicFns =
  MacawSymbolicArchFunctions
  { crucGenArchConstraints = \x -> x
  , crucGenRegAssignment = x86RegAssignment
  , crucGenArchRegName  = x86RegName
  , crucGenArchFn = crucGenX86Fn
  , crucGenArchStmt = crucGenX86Stmt
  , crucGenArchTermStmt = crucGenX86TermStmt
  }


-- | X86_64 specific function for evaluating a Macaw X86_64 program in Crucible.
x86_64MacawEvalFn
  :: C.IsSymInterface sym
  => SymFuns sym
  -> MacawArchEvalFn sym M.X86_64
x86_64MacawEvalFn fs =
  MacawArchEvalFn $ \global_var_mem globals ext_stmt crux_state ->
    case ext_stmt of
      X86PrimFn x -> funcSemantics fs x crux_state
      X86PrimStmt stmt -> stmtSemantics fs global_var_mem globals stmt crux_state
      X86PrimTerm term -> termSemantics fs term crux_state

x86LookupReg
  :: C.RegEntry sym (ArchRegStruct M.X86_64)
  -> M.X86Reg tp
  -> C.RegEntry sym (ToCrucibleType tp)
x86LookupReg reg_struct_entry macaw_reg =
  case lookupX86Reg macaw_reg (C.regValue reg_struct_entry) of
    Just (C.RV val) -> C.RegEntry (typeToCrucible $ M.typeRepr macaw_reg) val
    Nothing -> error $ "unexpected register: " ++ showF macaw_reg

x86UpdateReg
  :: C.RegEntry sym (ArchRegStruct M.X86_64)
  -> M.X86Reg tp
  -> C.RegValue sym (ToCrucibleType tp)
  -> C.RegEntry sym (ArchRegStruct M.X86_64)
x86UpdateReg reg_struct_entry macaw_reg val =
  case updateX86Reg macaw_reg (\_ -> C.RV val) (C.regValue reg_struct_entry) of
    Just res_reg_struct -> reg_struct_entry { C.regValue = res_reg_struct }
    Nothing -> error $ "unexpected register: " ++ showF macaw_reg

instance ArchInfo M.X86_64 where
  archVals _ = Just $ ArchVals
    { archFunctions = x86_64MacawSymbolicFns
    , withArchEval = \sym -> \k -> do
        sfns <- liftIO $ newSymFuns sym
        k $ x86_64MacawEvalFn sfns
    , withArchConstraints = \x -> x
    , lookupReg = x86LookupReg
    , updateReg = x86UpdateReg
    }
