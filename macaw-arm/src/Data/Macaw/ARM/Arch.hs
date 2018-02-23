{-# LANGUAGE ConstraintKinds #-}
{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}

{-# LANGUAGE StandaloneDeriving    #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE KindSignatures        #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE RankNTypes            #-}
{-# LANGUAGE ScopedTypeVariables   #-}
{-# LANGUAGE TypeApplications      #-}

module Data.Macaw.ARM.Arch
    -- ( ARMArchConstraints
    -- , ARMStmt(..)
    -- )
    where

import           Data.Macaw.ARM.ARMReg
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.CFG.Block as MCB
import           Data.Macaw.CFG.Rewriter ( Rewriter, rewriteValue, appendRewrittenArchStmt )
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Generator as G
import qualified Data.Macaw.SemMC.Operands as O
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.TraversableF as TF
import qualified Data.Parameterized.TraversableFC as FCls
import qualified Dismantle.ARM as D
import qualified Dismantle.ARM.Operands as ARMOperands
import           GHC.TypeLits
import qualified SemMC.ARM as ARM
import qualified Text.PrettyPrint.ANSI.Leijen as PP
import qualified Text.PrettyPrint.HughesPJClass as HPP

-- ----------------------------------------------------------------------
-- ARM-specific statement definitions

data ARMStmt (v :: MT.Type -> *) where
    WhatShouldThisBe :: ARMStmt v

type instance MC.ArchStmt ARM.ARM = ARMStmt

instance MC.IsArchStmt ARMStmt where
    ppArchStmt _pp stmt =
        case stmt of
          WhatShouldThisBe -> PP.text "arm_what?"

instance TF.FunctorF ARMStmt where
  fmapF = TF.fmapFDefault

instance TF.FoldableF ARMStmt where
  foldMapF = TF.foldMapFDefault

instance TF.TraversableF ARMStmt where
  traverseF go stmt =
    case stmt of
      WhatShouldThisBe -> pure WhatShouldThisBe

rewriteStmt :: (MC.ArchStmt arm ~ ARMStmt) =>
               ARMStmt (MC.Value arm src) -> Rewriter arm s src tgt ()
rewriteStmt s = appendRewrittenArchStmt =<< TF.traverseF rewriteValue s


-- ----------------------------------------------------------------------
-- ARM terminal statements (which have instruction-specific effects on
-- control-flow and register state).

data ARMTermStmt ids where
    ARMSyscall :: ARMOperands.SvcOperand -> ARMTermStmt ids

deriving instance Show (ARMTermStmt ids)

type instance MC.ArchTermStmt ARM.ARM = ARMTermStmt

instance MC.PrettyF ARMTermStmt where
    prettyF ts =
        case ts of
          ARMSyscall v -> let hpp2pp = PP.text . show . HPP.pPrint
                          -- ugh: dismantle uses HPP, Arch uses PP.
                          in PP.text "arm_syscall" PP.<+> hpp2pp v


-- instance PrettyF (ArchTermStmt ARM.ARM))

rewriteTermStmt :: ARMTermStmt src -> Rewriter arm s src tgt (ARMTermStmt tgt)
rewriteTermStmt s =
    case s of
      ARMSyscall v -> pure $ ARMSyscall v


-- ----------------------------------------------------------------------
-- ARM functions.  These may return a value, and may depend on the
-- current state of the heap and the set of registeres defined so far
-- and the result type, but should not affect the processor state.

-- type family ArchStmt (arch :: *) :: (Type -> *) -> *
-- data ARMStmt (v :: MT.Type -> *) where
--     WhatShouldThisBe :: ARMStmt v
-- type instance MC.ArchStmt ARM.ARM = ARMStmt

-- type family ArchFn :: (arch :: *) :: (Type -> *) -> Type -> *
-- data ARMPrimFn f (tp :: (MT.Type -> *) -> MT.Type) where
--     NoPrimKnown :: ARMPrimFn tp
data ARMPrimFn f tp where
    NoPrimKnown :: f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ARM.ARM))) -> ARMPrimFn f (MT.BVType (MC.RegAddrWidth (MC.ArchReg ARM.ARM)))

instance MC.IsArchFn ARMPrimFn where
  ppArchFn pp f =
      case f of
        NoPrimKnown rhs -> (\rhs' -> PP.text "arm_noprimknown " PP.<> rhs') <$> pp rhs

instance FCls.FunctorFC ARMPrimFn where
  fmapFC = FCls.fmapFCDefault

instance FCls.FoldableFC ARMPrimFn where
  foldMapFC = FCls.foldMapFCDefault

instance FCls.TraversableFC ARMPrimFn where
  traverseFC go f =
    case f of
      NoPrimKnown rhs -> NoPrimKnown <$> go rhs

type instance MC.ArchFn ARM.ARM = ARMPrimFn


-- no side effects... yet
armPrimFnHasSideEffects :: ARMPrimFn f tp -> Bool
armPrimFnHasSideEffects = const False


rewritePrimFn :: (ARMArchConstraints arm, MC.ArchFn arm ~ ARMPrimFn)
              => ARMPrimFn (MC.Value arm src) tp
              -> Rewriter arm s src tgt (MC.Value arm tgt tp)
rewritePrimFn f =
  case f of
    NoPrimKnown rhs -> error "No ARM rewritePrimFn for NoPrimKnown"
    _ -> error "No ARM rewritePrimFn for ??"


-- ----------------------------------------------------------------------
-- The aggregate set of architectural constraints to express for ARM
-- computations

type ARMArchConstraints arm = ( MC.ArchReg arm ~ ARMReg
                              , MC.ArchFn arm ~ ARMPrimFn
                              , MC.ArchStmt arm ~ ARMStmt
                              , MC.ArchTermStmt arm ~ ARMTermStmt
                              , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg arm))
                              , 1 <= MC.RegAddrWidth ARMReg
                              , KnownNat (MC.RegAddrWidth ARMReg)
                              , MC.ArchConstraints arm
                              , O.ExtractValue arm ARMOperands.GPR (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
                              , O.ExtractValue arm (Maybe ARMOperands.GPR) (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
                              )


-- ----------------------------------------------------------------------

-- | Manually-provided semantics for instructions whose full semantics cannot be
-- expressed in our semantics format.
--
-- This includes instructions with special side effects that we don't have a way
-- to talk about in the semantics; especially useful for architecture-specific
-- terminator statements.
armInstructionMatcher :: (ARMArchConstraints ppc) =>
                         D.Instruction -> Maybe (G.Generator ppc ids s ())
armInstructionMatcher (D.Instruction opc operands) =
  case opc of
    D.SVC -> case operands of
               D.Pred _opPred D.:< D.Imm24b imm D.:< D.Nil ->
                   Just $ G.finishWithTerminator (MCB.ArchTermStmt (ARMSyscall imm))
    _ -> Nothing
