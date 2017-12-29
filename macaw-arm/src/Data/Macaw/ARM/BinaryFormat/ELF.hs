{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE AllowAmbiguousTypes #-}

module Data.Macaw.ARM.BinaryFormat.ELF
    ( parseELFInfo
    , getELFSymbols
    -- , tocBaseForELF
    -- , tocEntryAddrsForElf
    )
    where

import Data.List (intercalate)
import Data.Vector (toList)
import Data.Bits
import Text.PrettyPrint.ANSI.Leijen
import           Control.Lens -- ((^.), (^..), filtered, over, folded, foldMapOf, to)
import           Control.Monad ( replicateM, unless )
import qualified Data.ByteString.Char8 as C8
import qualified Data.ElfEdit as E
import qualified Data.Macaw.AbsDomain.AbsState as MA
import qualified Data.Macaw.CFG as MC
import qualified Data.Macaw.Memory as MM
import           Data.Macaw.Types ( BVType )
import qualified Data.Map.Strict as M
import           Data.Proxy ( Proxy(..) )
import qualified Data.Serialize.Get as G
import qualified Data.Set as S
import           GHC.TypeLits ( KnownNat, natVal )


parseFunctionDescriptors :: (MM.MemWidth (MC.RegAddrWidth (MC.ArchReg ppc)))
                         => proxy ppc
                         -> Int
                         -> G.Get (M.Map (MM.MemAddr (MC.RegAddrWidth (MC.ArchReg ppc))) (MA.AbsValue (MC.RegAddrWidth (MC.ArchReg ppc)) (BVType (MC.RegAddrWidth (MC.ArchReg ppc)))))
parseFunctionDescriptors _ ptrSize = do
  let recordBytes = (3 * ptrSize) `div` 8
  let recordParser =
        case ptrSize of
          32 -> getFunctionDescriptor G.getWord32be
          64 -> getFunctionDescriptor G.getWord64be
          _ -> error ("Invalid pointer size: " ++ show ptrSize)
  totalBytes <- G.remaining
  unless (totalBytes `mod` recordBytes == 0) $ do
    fail "The .opd section is not divisible by the record size"
  funcDescs <- replicateM (totalBytes `div` recordBytes) recordParser
  return (M.fromList funcDescs)

getFunctionDescriptor :: (Integral a, MM.MemWidth w)
                      => G.Get a
                      -> G.Get (MM.MemAddr w, MA.AbsValue w (BVType w))
getFunctionDescriptor ptrParser = do
  entryAddr <- ptrParser
  tocAddr <- ptrParser
  _ <- ptrParser
  let mso = MM.absoluteAddr (fromIntegral entryAddr)
  return (mso, MA.FinSet (S.singleton (fromIntegral tocAddr)))


parseELFInfo :: forall arm proxy
          . (KnownNat (MC.RegAddrWidth (MC.ArchReg arm)), MM.MemWidth (MC.RegAddrWidth (MC.ArchReg arm)))
         => proxy arm
         -> E.Elf (MC.RegAddrWidth (MC.ArchReg arm))
         -> Either String (M.Map
                          (MM.MemAddr (MC.RegAddrWidth (MC.ArchReg arm)))
                          (MA.AbsValue (MC.RegAddrWidth (MC.ArchReg arm)) (BVType (MC.RegAddrWidth (MC.ArchReg arm)))))
parseELFInfo proxy e =
    let secnames = e^..E.elfSections.to (C8.unpack . E.elfSectionName)
    in Left $ intercalate ", " secnames
  -- Left $ e^..E.elfSections . foldMapOf folded (C8.unpack . E.elfSectionName)
  -- case E.findSectionByName (C8.pack ".opd") e of
  --   [sec] ->
  --     G.runGet (parseFunctionDescriptors proxy (fromIntegral ptrSize)) (E.elfSectionData sec)
  --   _ -> error "Could not find .opd section"
  -- where
  --   ptrSize = natVal (Proxy @(MC.RegAddrWidth (MC.ArchReg arm)))

-- getELFSymbols :: E.Elf (MC.RegAddrWidth (MC.ArchReg arm)) -> String
getELFSymbols :: (Show (E.ElfWordType w), Data.Bits.Bits (E.ElfWordType w), Integral (E.ElfWordType w)) => E.Elf w -> Doc
getELFSymbols elf =
    let dummy = 1
        -- symtab :: E.ElfSymbolTableEntry (E.ElfWordType (MC.RegAddrWidth (MC.ArchReg arm)))
        -- symtab :: E.ElfSymbolTableEntry (E.ElfWordType w)
        symtab = elf^.to E.elfSymtab
        ps = fmap (E.ppSymbolTableEntries . toList . E.elfSymbolTableEntries) symtab
        -- x = elf^.(E.elfSymtab).to (show . E.ppSymbolTableEntries)
    in vsep ps -- intercalate ", and " ps
