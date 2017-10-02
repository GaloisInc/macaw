{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GeneralizedNewtypeDeriving #-}
module Data.Macaw.PPC.Disassemble ( disassembleFn ) where

import qualified Control.Monad.Except as ET
import           Control.Monad.ST ( ST )
import           Control.Monad.Trans ( lift )

import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Nonce as NC

import           Data.Macaw.PPC.Generator

newtype DisM s a = DisM { unDisM :: ET.ExceptT DisassembleException (ST s) a }
  deriving (Functor,
            Applicative,
            Monad,
            ET.MonadError DisassembleException)

data DisassembleException = DisassembleException
  deriving (Show)

liftST :: ST s a -> DisM s a
liftST = DisM . lift

tryDisassembleBlock :: MM.Memory (ArchAddrWidth ppc)
                    -> NC.NonceGenerator (ST ids) ids
                    -> ArchSegmentOff ppc
                    -> ArchAddrWord ppc
                    -> DisM s ([Block ppc ids], MM.MemWord (ArchAddrWidth ppc))
tryDisassembleBlock = undefined

-- | Disassemble a block from the given start address (which points into the
-- 'MM.Memory').
--
-- Return a list of disassembled blocks as well as the total number of bytes
-- occupied by those blocks.
disassembleFn :: (MM.MemWidth (RegAddrWidth (ArchReg ppc)))
              => proxy ppc
              -> MM.Memory (ArchAddrWidth ppc)
              -> NC.NonceGenerator (ST ids) ids
              -> ArchSegmentOff ppc
              -- ^ The address to disassemble from
              -> ArchAddrWord ppc
              -- ^ Maximum size of the block (a safeguard)
              -> MA.AbsBlockState (ArchReg ppc)
              -- ^ Abstract state of the processor at the start of the block
              -> ST ids ([Block ppc ids], MM.MemWord (ArchAddrWidth ppc), Maybe String)
disassembleFn _ mem nonceGen startAddr maxSize _  = do
  mr <- ET.runExceptT (unDisM (tryDisassembleBlock mem nonceGen startAddr maxSize))
  case mr of
    Left exn -> return ([], 0, Just (show exn))
    Right (blocks, bytes) -> return (blocks, bytes, Nothing)
