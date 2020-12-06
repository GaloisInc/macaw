{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE RankNTypes #-}

module Shared (
  withELF64
  ) where

import qualified Data.ByteString as B

import qualified Data.ElfEdit as E

withELF64 :: FilePath -> (E.ElfHeaderInfo 64 -> IO ()) -> IO ()
withELF64 fp k = do
  bytes <- B.readFile fp
  case E.decodeElfHeaderInfo bytes of
    Left (off,err) ->
      error ("Error parsing ELF header at offset " ++ show off ++ ": " ++ err
            )
    Right (E.SomeElf e) ->
      case E.headerClass (E.header e) of
        E.ELFCLASS64 -> k e
        o -> error $ "Unsupported file type (wanted Elf64, got: " <> show o <> ")"
