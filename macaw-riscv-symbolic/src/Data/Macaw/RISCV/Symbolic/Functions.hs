{-# LANGUAGE EmptyCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Data.Macaw.RISCV.Symbolic.Functions
  ( SymFuns
  , newSymFuns
  , funcSemantics
  , stmtSemantics
  , termSemantics
  ) where

-- crucible
import qualified Lang.Crucible.Backend as C
import qualified Lang.Crucible.Simulator.ExecutionTree as C
import qualified Lang.Crucible.Simulator.RegMap as C
import qualified Lang.Crucible.Types as C

-- macaw-riscv
import qualified Data.Macaw.RISCV as MR

-- macaw-symbolic
import qualified Data.Macaw.Symbolic as MS

-- macaw-riscv-symbolic
import qualified Data.Macaw.RISCV.Symbolic.AtomWrapper as RA
import qualified Data.Macaw.RISCV.Symbolic.Panic as RP

data SymFuns sym = SymFuns

funcSemantics :: SymFuns sym
              -> MR.RISCVPrimFn rv (RA.AtomWrapper f) mt
              -> S p rv sym rtp bs r ctx
              -> IO (C.RegValue sym (MS.ToCrucibleType mt), S p rv sym rtp bs r ctx)
funcSemantics _sf pf _s =
  case pf of
    MR.RISCVEcall {} ->
      RP.panic RP.RISCV "funcSemantics" ["The RISC-V syscall primitive should be eliminated and replaced by a handle lookup"]

stmtSemantics :: SymFuns sym
              -> MR.RISCVStmt rv (RA.AtomWrapper (C.RegEntry sym))
              -> S p rv sym rtp bs r ctx
              -> IO (C.RegValue sym C.UnitType, S p rv sym rtp bs r ctx)
stmtSemantics _sf stmt _s = case stmt of {}

newSymFuns :: forall sym . (C.IsSymInterface sym) => sym -> IO (SymFuns sym)
newSymFuns _sym = pure SymFuns

termSemantics :: SymFuns sym
              -> MR.RISCVTermStmt rv (RA.AtomWrapper (C.RegEntry sym))
              -> S p rv sym rtp bs r ctx
              -> IO (C.RegValue sym C.UnitType, S p rv sym rtp bs r ctx)
termSemantics _fs term _s = case term of {}

type S p rv sym rtp bs r ctx = C.CrucibleState p sym (MS.MacawExt (MR.RISCV rv)) rtp bs r ctx
