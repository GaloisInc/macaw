{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE StandaloneDeriving #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.RISCV.Disassemble.Monad
  ( -- * Instruction disassembly
    DisInstM(..), runDisInstM
  , DisInstError(..)
  , DisInstState, disInstRegState, disInstRegUpdates
  , getDisInst, getDisInstBytes, getDisInstWord
  , getReg, readMem, evalApp
  , setReg, writeMem
  ) where

import qualified Control.Monad.Except as E
import qualified GRIFT.Types as G
import qualified GRIFT.Semantics as G
import qualified Data.Parameterized.Map as MapF
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Types as MT
import qualified Control.Monad.RWS as RWS
import qualified Data.Sequence as Seq

import           Control.Lens ( makeLenses
                              , view
                              , use
                              , assign
                              )
import           Control.Monad.ST (ST)
import           Control.Monad.Trans (lift)
import           Data.Parameterized.Nonce (NonceGenerator, freshNonce)

import           Data.Macaw.RISCV.RISCVReg ( )

-- | To disassemble the instruction, we need access to the
-- instruction, its size in bytes, and the integer it was decoded
-- from, along with a 'NonceGenerator' supplied by the caller.
data DisInstEnv s ids rv fmt = DisInstEnv { _disInst :: G.Instruction rv fmt
                                          , _disInstBytes :: Integer
                                          , _disInstWord :: Integer
                                          , _disNonceGen :: NonceGenerator (ST s) ids
                                          }
makeLenses ''DisInstEnv

-- | The state we maintain during instruction disassembly is two
-- 'MC.RegState' maps. The first is complete for every register and is
-- passed in by the caller, representing the register state in the
-- context of the block in which this instruction is executing. The
-- second only records the updates this particular instruction is
-- making to the register state.
data DisInstState (rv :: G.RV) ids = DisInstState {
  _disInstRegState :: MC.RegState (MC.ArchReg rv) (MC.Value rv ids),
  disInstRegUpdates :: MapF.MapF (MC.ArchReg rv) (MC.Value rv ids)
  }
makeLenses ''DisInstState

-- | Instruction disassembly error.
data DisInstError rv fmt = NonConstantGPR (G.InstExpr fmt rv 5)
                         | NonConstantFPR (G.InstExpr fmt rv 5)
                         | ZeroWidthExpr (G.InstExpr fmt rv 0)
                         | forall w . BadExprWidth (G.InstExpr fmt rv w)
                         | GenericError String

instance Show (DisInstError rv fmt) where
  show (NonConstantGPR _e) = "NonConstantGPR in expression"
  show (NonConstantFPR _e) = "NonConstantFPR in expression"
  show (ZeroWidthExpr _e) = "Expression has width zero"
  show (BadExprWidth _e) = "Bad expression width"
  show (GenericError s) = s

-- | Monad for disassembling a single instruction.
newtype DisInstM s ids rv fmt a = DisInstM
  { unDisInstM :: E.ExceptT (DisInstError rv fmt) (RWS.RWST (DisInstEnv s ids rv fmt) (Seq.Seq (MC.Stmt rv ids)) (DisInstState rv ids) (ST s)) a }
  deriving ( Functor
           , Applicative
           , Monad
           , RWS.MonadReader (DisInstEnv s ids rv fmt)
           , RWS.MonadWriter (Seq.Seq (MC.Stmt rv ids))
           , RWS.MonadState (DisInstState rv ids)
           , E.MonadError (DisInstError rv fmt)
           )

runDisInstM :: G.Instruction rv fmt
            -- ^ The instruction we are disassembling
            -> Integer
            -- ^ The size of the instruction, in bytes
            -> Integer
            -- ^ The original, undecoded instruction word
            -> NonceGenerator (ST s) ids
            -- ^ The nonce generator used for block disassembly
            -> MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
            -- ^ The block's register state at the start of the instruction
            -> DisInstM s ids rv fmt a
            -> ST s (Either (DisInstError rv fmt) a, DisInstState rv ids, Seq.Seq (MC.Stmt rv ids))
runDisInstM inst instBytes instWord ng blockRegState action =
  RWS.runRWST (E.runExceptT (unDisInstM action)) env st
  where env = DisInstEnv inst instBytes instWord ng
        st  = DisInstState blockRegState MapF.empty

getDisInst :: DisInstM s ids rv fmt (G.Instruction rv fmt)
getDisInst = view disInst

getDisInstBytes :: DisInstM s ids rv fmt Integer
getDisInstBytes = view disInstBytes

getDisInstWord :: DisInstM s ids rv fmt Integer
getDisInstWord = view disInstWord

liftST :: ST s a -> DisInstM s ids rv fmt a
liftST = DisInstM . lift . lift

addAssignment :: MC.AssignRhs rv (MC.Value rv ids) tp
              -> DisInstM s ids rv fmt (MC.Value rv ids tp)
addAssignment rhs = do
  ng <- view disNonceGen
  nonce <- liftST $ freshNonce ng
  let asgn = MC.Assignment (MC.AssignId nonce) rhs
  addStmt (MC.AssignStmt asgn)
  return (MC.AssignedValue asgn)

evalApp :: MC.App (MC.Value rv ids) tp
        -> DisInstM s ids rv fmt (MC.Value rv ids tp)
evalApp = addAssignment . MC.EvalApp

readMem :: MC.Value rv ids (MT.BVType (MC.ArchAddrWidth rv))
        -> MC.MemRepr tp
        -> DisInstM s ids rv fmt (MC.Value rv ids tp)
readMem addr bytes = addAssignment $ MC.ReadMem addr bytes

-- FIXME: This is wrong. What we really want to do is reference the
-- value of the register before executing the instruction. See JALR as
-- an example -- if the link register is equal to the register
-- containing the jump address, then things are going to go bad
getReg :: MC.ArchReg rv tp -> DisInstM s ids rv fmt (MC.Value rv ids tp)
getReg r = use (disInstRegState . MC.boundValue r)

setReg :: MC.ArchReg rv tp -> MC.Value rv ids tp -> DisInstM s ids rv fmt ()
setReg r v = do
  RWS.modify $ \s -> s { disInstRegUpdates = MapF.insert r v (disInstRegUpdates s) }
  assign (disInstRegState . MC.boundValue r) v

addStmt :: MC.Stmt rv ids -> DisInstM s ids rv fmt ()
addStmt stmt = RWS.tell (Seq.singleton stmt)

writeMem :: MC.ArchAddrValue rv ids
         -> MC.MemRepr tp
         -> MC.Value rv ids tp
         -> DisInstM s ids rv fmt ()
writeMem addr bytes val = addStmt (MC.WriteMem addr bytes val)
