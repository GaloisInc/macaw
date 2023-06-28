{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE TypeApplications #-}
module Data.Macaw.Discovery.Classifier.JumpTable (
  jumpTableClassifier
  ) where

import           Control.Applicative ( Alternative((<|>)) )
import           Control.Lens ( (&), (^.) )
import           Control.Monad ( when, unless )
import qualified Control.Monad.Reader as CMR
import qualified Data.ByteString as BS
import qualified Data.Foldable as F
import           Data.Int ( Int32, Int64 )
import qualified Data.Map.Strict as Map
import           Data.Parameterized.Classes
import           Data.Parameterized.NatRepr
import           Data.Set (Set)
import qualified Data.Set as Set
import qualified Data.Traversable as T
import qualified Data.Vector as V
import           Data.Word ( Word64 )
import           Numeric ( showHex )
import           Numeric.Natural ( Natural )
import qualified Prettyprinter as PP

import qualified Data.Macaw.Architecture.Info as Info
import           Data.Macaw.AbsDomain.AbsState
import qualified Data.Macaw.AbsDomain.JumpBounds as Jmp
import qualified Data.Macaw.AbsDomain.StridedInterval as SI
import           Data.Macaw.CFG
import qualified Data.Macaw.Discovery.ParsedContents as Parsed
import qualified Data.Macaw.Memory.Permissions as Perm
import           Data.Macaw.Types

--------------------------------------------------------------------------------
-- Jump table recognition

-- | `extendDyn ext end bs` parses the bytestring using the extension
-- and endianness information, and returns the extended value.
extendDyn :: Parsed.Extension w -> Endianness -> BS.ByteString -> Integer
extendDyn (Parsed.Extension False Addr32) end bs  = toInteger (bsWord32 end bs)
extendDyn (Parsed.Extension False Addr64) end bs  = toInteger (bsWord64 end bs)
extendDyn (Parsed.Extension True  Addr32) end bs = toInteger (fromIntegral (bsWord32 end bs) :: Int32)
extendDyn (Parsed.Extension True  Addr64) end bs = toInteger (fromIntegral (bsWord64 end bs) :: Int64)

-- This function resolves jump table entries.
-- It is a recursive function that has an index into the jump table.
-- If the current index can be interpreted as a intra-procedural jump,
-- then it will add that to the current procedure.
-- This returns the last address read.
resolveRelativeJumps :: forall arch w
                        .  ( MemWidth (ArchAddrWidth arch)
                        , IPAlignment arch
                        , RegisterInfo (ArchReg arch)
                        )
                     => Memory (ArchAddrWidth arch)
                     -> ArchSegmentOff arch
                     -> Parsed.BoundedMemArray arch (BVType w)
                     -> Parsed.Extension w
                     -> Either String (V.Vector (ArchSegmentOff arch))
resolveRelativeJumps mem base arrayRead ext = do
  let slices = Parsed.arSlices arrayRead
  let BVMemRepr _ endianness = Parsed.arEltType arrayRead
  T.forM slices $ \l -> do
    bs <- case l of
            [ByteRegion bs] -> Right bs
            _ -> Left $ "Could not recognize slice: " <> show l
    let tgtAddr = segoffAddr base & incAddr (extendDyn ext endianness bs)

    let brRepr = unwords [ showHex w "" | w <- BS.unpack bs ]

    tgt <- case asSegmentOff mem (toIPAligned @arch tgtAddr) of
             Just tgt -> Right tgt
             _ -> Left $ "Could not resolve " <> show (ext, endianness, base, brRepr)

    unless (Perm.isExecutable (segmentFlags (segoffSegment tgt))) $ do
      Left "Address is not executable."

    Right tgt

sliceMemContents'
  :: MemWidth w
  => Int -- ^ Number of bytes in each slice.
  -> [[MemChunk w]] -- ^ Previous slices
  -> Integer -- ^ Number of slices to return
  -> [MemChunk w] -- ^ Ranges to process next
  -> Either (SplitError w) ([[MemChunk w]],[MemChunk w])
sliceMemContents' stride prev c next
  | c <= 0 = pure (reverse prev, next)
  | otherwise =
    case splitMemChunks next stride of
      Left e -> Left e
      Right (this, rest) -> sliceMemContents' stride (this:prev) (c-1) rest

-- | @sliceMemContents stride cnt contents@ splits contents up into @cnt@
-- memory regions each with size @stride@.
sliceMemContents
  :: MemWidth w
  => Int -- ^ Number of bytes in each slice.
  -> Integer -- ^ Number of slices to return
  -> [MemChunk w] -- ^ Ranges to process next
  -> Either (SplitError w) ([[MemChunk w]],[MemChunk w])
sliceMemContents stride c next = sliceMemContents' stride [] c next

-------------------------------------------------------------------------------
-- BoundedMemArray recognition

absValueAsSegmentOff
  :: forall w
  .  Memory w
  -> AbsValue w (BVType  w)
  -> Maybe (MemSegmentOff w)
absValueAsSegmentOff mem av = case av of
  FinSet s | Set.size s == 1 -> resolveAbsoluteIntegerAddr (shead s)
  CodePointers s False | Set.size s == 1 -> Just (shead s)
  CodePointers s True  | Set.size s == 0 -> resolveAbsoluteIntegerAddr 0
  StridedInterval si -> SI.isSingleton si >>= resolveAbsoluteIntegerAddr
  _ -> Nothing
  where
  shead :: Set a -> a
  shead = Set.findMin

  resolveAbsoluteIntegerAddr :: Integer -> Maybe (MemSegmentOff w)
  resolveAbsoluteIntegerAddr = resolveAbsoluteAddr mem . addrWidthClass (memAddrWidth mem) fromInteger

-- | This attempts to interpret a value as a memory segment offset
-- using the memory and abstract interpretation of value.
valueAsSegmentOffWithTransfer
  :: forall arch ids
  .  RegisterInfo (ArchReg arch)
  => Memory (ArchAddrWidth arch)
  -> AbsProcessorState (ArchReg arch) ids
  -> BVValue arch ids (ArchAddrWidth arch)
  -> Maybe (ArchSegmentOff arch)
valueAsSegmentOffWithTransfer mem aps base
  =   valueAsSegmentOff mem base
  <|> absValueAsSegmentOff mem (transferValue aps base)

-- | This attempts to pattern match a value as a memory address plus a value.
valueAsMemOffset
  :: RegisterInfo (ArchReg arch)
  => Memory (ArchAddrWidth arch)
  -> AbsProcessorState (ArchReg arch) ids
  -> ArchAddrValue arch ids
  -> Maybe (ArchSegmentOff arch, ArchAddrValue arch ids)
valueAsMemOffset mem aps v
  | Just (BVAdd _ base offset) <- valueAsApp v
  , Just ptr <- valueAsSegmentOffWithTransfer mem aps base
  = Just (ptr, offset)

  -- and with the other argument order
  | Just (BVAdd _ offset base) <- valueAsApp v
  , Just ptr <- valueAsSegmentOffWithTransfer mem aps base
  = Just (ptr, offset)

  | otherwise = Nothing

-- This function resolves jump table entries.
-- It is a recursive function that has an index into the jump table.
-- If the current index can be interpreted as a intra-procedural jump,
-- then it will add that to the current procedure.
-- This returns the last address read.
resolveAsAddr :: forall w
              .  Memory w
              -> Endianness
              -> [MemChunk w]
              -> Maybe (MemAddr w)
resolveAsAddr mem endianness l = addrWidthClass (memAddrWidth mem) $
  case l of
    [ByteRegion bs] ->
      case addrRead endianness bs of
        Just a -> pure $! absoluteAddr a
        Nothing -> error $ "internal: resolveAsAddr given short chunk list."
    [RelocationRegion r] -> do
        when (relocationIsRel r) $ Nothing
        case relocationSym r of
          SymbolRelocation{} -> Nothing
          SectionIdentifier idx -> do
            addr <- Map.lookup idx (memSectionIndexMap mem)
            pure $! segoffAddr addr & incAddr (toInteger (relocationOffset r))
          SegmentBaseAddr idx -> do
            seg <- Map.lookup idx (memSegmentIndexMap mem)
            pure $! segmentOffAddr seg (relocationOffset r)
          LoadBaseAddr -> do
            memBaseAddr mem
    _ -> Nothing

-- | Just like Some (BVValue arch ids), but doesn't run into trouble with
-- partially applying the BVValue type synonym.
data SomeExt arch ids = forall m . SomeExt !(BVValue arch ids m) !(Parsed.Extension m)

matchAddr :: NatRepr w -> Maybe (AddrWidthRepr w)
matchAddr w
  | Just Refl <- testEquality w n32 = Just Addr32
  | Just Refl <- testEquality w n64 = Just Addr64
  | otherwise = Nothing

-- | @matchExtension x@ matches in @x@ has the form @uext y w@ or @sext y w@ and returns
-- a description about the extension as well as the pattern @y@.
matchExtension :: forall arch ids
               .  ( MemWidth (ArchAddrWidth arch)
                  , HasRepr (ArchReg arch) TypeRepr)
               => ArchAddrValue arch ids
               -> SomeExt arch ids
matchExtension val =
  case valueAsApp val of
    Just (SExt val' _w) | Just repr <- matchAddr (typeWidth val') -> SomeExt val' (Parsed.Extension True  repr)
    Just (UExt val' _w) | Just repr <- matchAddr (typeWidth val') -> SomeExt val' (Parsed.Extension False repr)
    _ -> SomeExt val (Parsed.Extension False (addrWidthRepr @(ArchAddrWidth arch) undefined))

-- | Contains information about jump table layout, addresses and index
-- in a recognized jump table.
type JumpTableClassifierResult arch ids =
   (Parsed.JumpTableLayout arch, V.Vector (ArchSegmentOff arch), ArchAddrValue arch ids)

type JumpTableClassifier arch ids s =
  Info.BlockClassifierM arch ids (JumpTableClassifierResult arch ids)

-- | This operation extracts chunks of memory for a jump table.
extractJumpTableSlices :: ArchConstraints arch
                       => Jmp.IntraJumpBounds arch ids
                       -- ^ Bounds for jump table
                       -> MemSegmentOff (ArchAddrWidth arch) -- ^ Base address
                       -> Natural -- ^ Stride
                       -> BVValue arch ids idxWidth
                       -> MemRepr tp -- ^ Type of values
                       -> Info.Classifier arch (V.Vector [MemChunk (ArchAddrWidth arch)])
extractJumpTableSlices jmpBounds base stride ixVal tp = do
  cnt <-
    case Jmp.unsignedUpperBound jmpBounds ixVal of
      Nothing -> fail $ "Upper bounds failed:\n"
                      ++ show (ppValueAssignments ixVal) ++ "\n"
                      ++ show (PP.pretty jmpBounds)
      Just bnd -> do
        let cnt = toInteger (bnd+1)
        -- Check array actually fits in memory.
        when (cnt * toInteger stride > segoffBytesLeft base) $ do
          fail "Size is too large."
        pure cnt

  -- Get memory contents after base
  Right contents <- pure $ segoffContentsAfter base
  -- Break up contents into a list of slices each with size stide
  Right (strideSlices,_) <- pure $ sliceMemContents (fromIntegral stride) cnt contents
  -- Get memory slices
  Right slices <-
    pure $ traverse (\s -> fst <$> splitMemChunks s (fromIntegral (memReprBytes tp)))
                    (V.fromList strideSlices)
  pure slices

-- | @matchBoundedMemArray mem aps bnds val@ checks to try to interpret
-- @val@ as a memory read where
--
-- * the address read has the form @base + stride * ixVal@,
-- * @base@ is a valid `MemSegmentOff`,
-- * @stride@ is a natural number and,
-- * @ixVal@ is a arbitrary value.
matchBoundedMemArray
  :: ArchConstraints arch
  => Memory (ArchAddrWidth arch)
  -> AbsProcessorState (ArchReg arch) ids
  -> Jmp.IntraJumpBounds arch ids
     -- ^ Bounds for jump table
  -> Value arch ids tp  -- ^ Value to interpret
  -> Info.Classifier arch (Parsed.BoundedMemArray arch tp, ArchAddrValue arch ids)
matchBoundedMemArray mem aps jmpBounds val = do
  AssignedValue (Assignment _ (ReadMem addr tp)) <- pure val
  Just (base, offset) <- pure $ valueAsMemOffset mem aps addr
  Just (stride, ixVal) <- pure $ valueAsStaticMultiplication offset
   -- Check stride covers at least number of bytes read.
  when (memReprBytes tp > stride) $ do
    fail "Stride does not cover size of relocation."
  -- Convert stride to word64 (must be lossless due to as memory is at most 64-bits)
  let stridew :: Word64
      stridew = fromIntegral stride
  -- Take the given number of bytes out of each slices
  slices <- extractJumpTableSlices jmpBounds base stride ixVal tp

  let r = Parsed.BoundedMemArray
          { Parsed.arBase     = base
          , Parsed.arStride   = stridew
          , Parsed.arEltType  = tp
          , Parsed.arSlices   = slices
          }
  pure  (r, ixVal)

-- | @matchAbsoluteJumpTable@ tries to match the control flow transfer
-- as a jump table where the addresses in the jump table are absolute
-- memory addresses.
matchAbsoluteJumpTable
  :: forall arch ids s
  .  ArchConstraints arch
  => JumpTableClassifier arch ids s
matchAbsoluteJumpTable = Info.classifierName "Absolute jump table" $ do
  bcc <- CMR.ask
  let mem = Info.pctxMemory (Info.classifierParseContext bcc)
  let aps = Info.classifierAbsState bcc
  let jmpBounds = Info.classifierJumpBounds bcc
  -- Get IP value to interpret as a jump table index.
  let ip = Info.classifierFinalRegState bcc^.curIP
  (arrayRead, idx) <- Info.liftClassifier $ matchBoundedMemArray mem aps jmpBounds ip
  unless (Parsed.isReadOnlyBoundedMemArray arrayRead) $ do
    fail "Bounded mem array is not read only."
  endianness <-
    case Parsed.arEltType arrayRead of
      BVMemRepr _arByteCount e -> pure e
  let go :: Int
         -> [MemChunk (ArchAddrWidth arch)]
         -> Info.Classifier arch (MemSegmentOff (ArchAddrWidth arch))
      go entryIndex contents = do
        addr <- case resolveAsAddr mem endianness contents of
                  Just a -> pure a
                  Nothing -> fail "Could not resolve jump table contents as absolute address."
        tgt <- case asSegmentOff mem (toIPAligned @arch addr) of
                 Just t -> pure t
                 Nothing ->
                   fail $
                     "Could not resolve jump table entry " ++ show entryIndex
                     ++ " value " ++ show addr ++ " as segment offset.\n" ++ show mem
        unless (Perm.isExecutable (segmentFlags (segoffSegment tgt))) $
          fail $ "Jump table contents non-executable."
        pure tgt
  tbl <- Info.liftClassifier $ V.zipWithM go (V.generate (V.length (Parsed.arSlices arrayRead)) id) (Parsed.arSlices arrayRead)
  pure (Parsed.AbsoluteJumpTable arrayRead, tbl, idx)

-- | @matchAbsoluteJumpTable@ tries to match the control flow transfer
-- as a jump table where the addresses in the jump table are IP relative jumps.
matchRelativeJumpTable
  :: forall arch ids s
  .  ArchConstraints arch
  => JumpTableClassifier arch ids s
matchRelativeJumpTable = Info.classifierName "Relative jump table" $ do
  bcc <- CMR.ask
  let mem = Info.pctxMemory (Info.classifierParseContext bcc)
  let aps = Info.classifierAbsState bcc
  let jmpBounds = Info.classifierJumpBounds bcc
  -- Get IP value to interpret as a jump table index.
  let ip = Info.classifierFinalRegState bcc^.curIP

  -- gcc-style PIC jump tables on x86 use, roughly,
  --     ip = jmptbl + jmptbl[index]
  -- where jmptbl is a pointer to the lookup table.
  Just unalignedIP <- pure $ fromIPAligned ip
  (tgtBase, tgtOffset) <-
    case valueAsMemOffset mem aps unalignedIP of
      Just p -> pure p
      Nothing -> fail $ "Unaligned IP not a mem offset: " <> show unalignedIP
  SomeExt shortOffset ext <- pure $ matchExtension tgtOffset
  (arrayRead, idx) <- Info.liftClassifier $ matchBoundedMemArray mem aps jmpBounds shortOffset
  unless (Parsed.isReadOnlyBoundedMemArray arrayRead) $ do
    fail $ "Jump table memory array must be read only."
  tbl <- case resolveRelativeJumps mem tgtBase arrayRead ext of
           Left msg -> fail msg
           Right tbl -> pure tbl
  pure (Parsed.RelativeJumpTable tgtBase arrayRead ext, tbl, idx)

-- | A classifier for jump tables
--
-- This classifier employs a number of heuristics, but is of course incomplete
jumpTableClassifier :: forall arch ids . Info.BlockClassifier arch ids
jumpTableClassifier = Info.classifierName "Jump table" $ do
  bcc <- CMR.ask
  let ctx = Info.classifierParseContext bcc
  let ainfo = Info.pctxArchInfo ctx
  let jmpBounds = Info.classifierJumpBounds bcc
  Info.withArchConstraints ainfo $ do
    let jumpTableClassifiers
          =   matchAbsoluteJumpTable
          <|> matchRelativeJumpTable
    (layout, entries, jumpIndex) <- jumpTableClassifiers

    let abst :: AbsBlockState (ArchReg arch)
        abst = finalAbsBlockState (Info.classifierAbsState bcc) (Info.classifierFinalRegState bcc)
    let nextBnds = Jmp.postJumpBounds jmpBounds (Info.classifierFinalRegState bcc)
    let term = Parsed.ParsedLookupTable layout (Info.classifierFinalRegState bcc) jumpIndex entries
    pure $ seq abst $
      Parsed.emptyParsedContents { Parsed.parsedNonterm = F.toList (Info.classifierStmts bcc)
                         , Parsed.parsedTerm = term
                         , Parsed.writtenCodeAddrs = Info.classifierWrittenAddrs bcc
                         , Parsed.intraJumpTargets =
                           [ (tgtAddr, abst & setAbsIP tgtAddr, nextBnds)
                           | tgtAddr <- V.toList entries
                           ]
                         , Parsed.newFunctionAddrs = []
                         }
