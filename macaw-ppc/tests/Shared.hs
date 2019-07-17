{-# LANGUAGE DataKinds #-}
module Shared (
  withELF
  ) where

import qualified Data.ByteString as B

import qualified Data.ElfEdit as E

withELF :: FilePath -> (E.Elf 64 -> IO ()) -> IO ()
withELF fp k = do
  bytes <- B.readFile fp
  E.parseElfOrDie (error "ELF32 is unsupported in the test suite") k bytes
