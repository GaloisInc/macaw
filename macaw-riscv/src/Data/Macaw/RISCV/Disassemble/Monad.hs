{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE RankNTypes #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE TypeOperators #-}

module Data.Macaw.RISCV.Disassemble.Monad
  ( DisInstM(..)
  , DisInstEnv, disInst, disInstBytes, disInstWord
  , DisInstError(..)
  , getReg, readMem, evalApp
  , setReg, writeMem
  ) where

import qualified Control.Monad.Except as E
import qualified GRIFT.Types as G
import qualified GRIFT.Semantics as G
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
import           Data.Parameterized.NatRepr
import           Data.Parameterized.Nonce (NonceGenerator, freshNonce)

import           Data.Macaw.RISCV.RISCVReg ()

data DisInstEnv s ids rv fmt = DisInstEnv { _disInst :: G.Instruction rv fmt
                                          , _disInstBytes :: Integer
                                          , _disInstWord :: Integer
                                          , _disNonceGen :: NonceGenerator (ST s) ids
                                          }
makeLenses ''DisInstEnv

data DisInstState (rv :: G.RV) ids = DisInstState { _disRegState :: MC.RegState (MC.ArchReg rv) (MC.Value rv ids)
                                                  }
makeLenses ''DisInstState

data DisInstError rv fmt = NonConstantGPR (G.InstExpr fmt rv 5)
                         | NonConstantFPR (G.InstExpr fmt rv 5)
                         | ZeroWidthExpr (G.InstExpr fmt rv 0)
                         | forall w w' . WidthNotLTExpr (G.InstExpr fmt rv w) (NatRepr w')

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

getReg :: MC.ArchReg rv tp -> DisInstM s ids rv fmt (MC.Value rv ids tp)
getReg r = use (disRegState . MC.boundValue r)

setReg :: MC.ArchReg rv tp -> MC.Value rv ids tp -> DisInstM s ids rv fmt ()
setReg r v = assign (disRegState . MC.boundValue r) v

addStmt :: MC.Stmt rv ids -> DisInstM s ids rv fmt ()
addStmt stmt = RWS.tell (Seq.singleton stmt)

writeMem :: MC.ArchAddrValue rv ids
         -> MC.MemRepr tp
         -> MC.Value rv ids tp
         -> DisInstM s ids rv fmt ()
writeMem addr bytes val = addStmt (MC.WriteMem addr bytes val)
