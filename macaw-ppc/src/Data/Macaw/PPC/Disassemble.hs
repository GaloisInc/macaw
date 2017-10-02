module Data.Macaw.PPC.Disassemble ( disassembleFn ) where

import           Control.Monad.ST ( ST )

import           Data.Macaw.AbsDomain.AbsState as MA
import           Data.Macaw.CFG
import           Data.Macaw.CFG.Block
import qualified Data.Macaw.Memory as MM
import qualified Data.Parameterized.Nonce as NC

disassembleFn :: proxy ppc
              -> MM.Memory (ArchAddrWidth ppc)
              -> NC.NonceGenerator (ST ids) ids
              -> ArchSegmentOff ppc
              -> ArchAddrWord ppc
              -> MA.AbsBlockState (ArchReg ppc)
              -> ST ids ([Block ppc ids], MM.MemWord (ArchAddrWidth ppc), Maybe String)
disassembleFn = undefined
