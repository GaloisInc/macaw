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
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.SemMC.Operands as O
import qualified Data.Macaw.Types as MT
import qualified Data.Parameterized.TraversableFC as FCls
import qualified Dismantle.ARM as D
import           GHC.TypeLits
import qualified SemMC.ARM as ARM
import qualified Text.PrettyPrint.ANSI.Leijen as PP

-- ----------------------------------------------------------------------
-- ARM-specific statement definitions

data ARMStmt (v :: MT.Type -> *) where
    WhatShouldThisBe :: ARMStmt v

type instance MC.ArchStmt ARM.ARM = ARMStmt

instance MC.IsArchStmt ARMStmt where
    ppArchStmt pp stmt =
        case stmt of
          WhatShouldThisBe -> PP.text "arm_what?"

-- ----------------------------------------------------------------------
-- ARM terminal statements (which have instruction-specific effects on
-- control-flow and register state).

data ARMTermStmt ids where
    ARMSyscall :: ARMTermStmt ids

deriving instance Show (ARMTermStmt ids)

type instance MC.ArchTermStmt ARM.ARM = ARMTermStmt

instance MC.PrettyF ARMTermStmt where
    prettyF ts =
        case ts of
          ARMSyscall -> PP.text "arm_syscall"

-- instance PrettyF (ArchTermStmt ARM.ARM))

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

-- ----------------------------------------------------------------------
-- The aggregate set of architectural constraints to express for ARM
-- computations

type ARMArchConstraints arm = ( MC.ArchReg arm ~ ARMReg
                              , MC.ArchFn arm ~ ARMPrimFn
                              , MC.ArchStmt arm ~ ARMStmt
                              -- , MC.ArchTermStmt arm ~ ARMTermStmt
                              -- , ArchWidth arm
                              , MM.MemWidth (MC.RegAddrWidth (MC.ArchReg arm))
                              , 1 <= MC.RegAddrWidth ARMReg
                              , KnownNat (MC.RegAddrWidth ARMReg)
                              , MC.ArchConstraints arm
                              -- , O.ExtractValue arm D.GPR (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
                              -- , O.ExtractValue arm (Maybe D.GPR) (MT.BVType (MC.RegAddrWidth (MC.ArchReg arm)))
                              )
