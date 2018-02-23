{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Shared (
  withELF,
  withMemory,
  findEntryPoint64
  ) where

import qualified Control.Monad.Catch as C
import qualified Data.ByteString as B
import           Data.Typeable ( Typeable )

import qualified Data.ElfEdit as E

import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MM

-- | Given an Elf object and the corresponding Memory object, find the address of the
-- correct entry point to the program
findEntryPoint64 :: E.Elf 64 -> MM.Memory 64 -> MM.MemAddr 64
findEntryPoint64 elf mem = case E.elfMachine elf of
  E.EM_PPC64 ->
    let startEntry = E.elfEntry elf
        Right addr = MM.readAddr mem MM.BigEndian (MM.absoluteAddr (MM.memWord (fromIntegral (startEntry))))
    in addr
  _          -> MM.absoluteAddr (MM.memWord (fromIntegral (E.elfEntry elf)))

withELF :: FilePath -> (E.Elf 64 -> IO ()) -> IO ()
withELF fp k = do
  bytes <- B.readFile fp
  case E.parseElf bytes of
    E.ElfHeaderError off msg ->
      error ("Error parsing ELF header at offset " ++ show off ++ ": " ++ msg)
    E.Elf32Res [] _e32 -> error "ELF32 is unsupported in the test suite"
    E.Elf64Res [] e64 -> k e64
    E.Elf32Res errs _ -> error ("Errors while parsing ELF file: " ++ show errs)
    E.Elf64Res errs _ -> error ("Errors while parsing ELF file: " ++ show errs)

withMemory :: forall w m a
            . (C.MonadThrow m, MM.MemWidth w, Integral (E.ElfWordType w))
           => MM.AddrWidthRepr w
           -> E.Elf w
           -> (MM.Memory w -> m a)
           -> m a
withMemory _ e k =
  case MM.memoryForElf loadCfg e of
    Left err -> C.throwM (MemoryLoadError err)
    Right (_sim, mem) -> k mem
  where
    loadCfg = MM.LoadOptions { MM.loadStyleOverride = Just MM.LoadBySegment
                             , MM.includeBSS = False
                             , MM.loadRegionIndex = Just 0
                             }

data ElfException = MemoryLoadError String
  deriving (Typeable, Show)

instance C.Exception ElfException
