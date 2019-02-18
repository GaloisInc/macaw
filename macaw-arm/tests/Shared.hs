{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE RankNTypes #-}
module Shared
    ( withELF
    , withMemory
    , findEntryPoint
    , ElfException(..)
    )
    where


import qualified Control.Monad.Catch as C
import           Data.Binary.Get (ByteOffset)
import qualified Data.ByteString as B
import qualified Data.ElfEdit as E
import           Data.List (intercalate)
import qualified Data.Macaw.Memory as MM
import qualified Data.Macaw.Memory.ElfLoader as MM
import           Data.Typeable ( Typeable )


-- | Given an Elf object and the corresponding Memory object, find the
-- address of the correct entry point to the program
findEntryPoint :: (MM.MemWidth w, Integral (E.ElfWordType w))
                   => E.Elf w -> MM.Memory w -> MM.MemAddr w
findEntryPoint elf mem =
    let startEntry = E.elfEntry elf
        absEntry = MM.absoluteAddr $ MM.memWord $ fromIntegral $ startEntry
        endian = case E.elfData elf of
                   E.ELFDATA2LSB -> MM.LittleEndian
                   E.ELFDATA2MSB -> MM.BigEndian
        Right derefEntry = MM.readAddr mem endian absEntry
    in case E.elfMachine elf of
         E.EM_PPC -> derefEntry  -- PPC entrypoint is a table reference
         _        -> absEntry


-- | Invokes the continuation with the parsed results of reading the
-- specified file, or generates an error exception of type ElfException.
withELF :: FilePath -> (forall w. E.Elf w -> IO ()) -> IO ()
withELF fp k = do
  bytes <- B.readFile fp
  case E.parseElf bytes of
    E.Elf32Res [] e32 -> k e32
    E.Elf64Res [] e64 -> k e64
    E.ElfHeaderError off msg -> C.throwM $ ElfHeaderParseError fp off msg
    E.Elf32Res errs _ -> C.throwM $ ElfParseError fp $ intercalate "; " $ map show errs
    E.Elf64Res errs _ -> C.throwM $ ElfParseError fp $ intercalate "; " $ map show errs


-- | Invokes the callback with a Macaw Memory representation of the
-- indicated Elf object.
withMemory :: forall w m a
            . (C.MonadThrow m, MM.MemWidth w, Integral (E.ElfWordType w))
           => MM.AddrWidthRepr w
           -> E.Elf w
           -> (MM.Memory w -> m a)
           -> m a
withMemory _ e k =
    let options = MM.LoadOptions { MM.loadRegionIndex = Just 0
                                 , MM.loadRegionBaseOffset = 0
                                 }
    in case MM.memoryForElf options e of
         Left err -> C.throwM (MemoryLoadError err)
         Right (mem, _sym, _warn, _err) -> k mem


data ElfException = MemoryLoadError String
                  | ElfParseError FilePath String
                  | ElfHeaderParseError FilePath ByteOffset String
  deriving (Typeable, Show)

instance C.Exception ElfException
