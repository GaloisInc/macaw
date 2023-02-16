{-# LANGUAGE DataKinds #-}
{-# LANGUAGE FlexibleContexts #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE UndecidableInstances #-}

-- | Functionality for computing the names and addresses of PLT stub functions
-- in a dynamically linked ELF binary.
--
-- Note that the API in this library is somewhat experimental, and as we further
-- develop the underlying heuristics involved (see @Note [PLT stub names]@), we
-- may need to change the API accordingly.
module Data.Macaw.Memory.ElfLoader.PLTStubs
  ( PLTStubInfo(..)
  , pltStubSymbols
  , noPLTStubInfo
  , NoRelocationType(..)
  ) where

import qualified Data.ByteString.Char8 as BSC
import qualified Data.ElfEdit as EE
import           Data.Foldable (Foldable(..))
import qualified Data.Map as Map
import           Data.Maybe ( fromMaybe, listToMaybe )
import           Data.Word ( Word32 )
import           GHC.TypeLits ( Nat )

import qualified Data.Macaw.Memory as DMM
import qualified Data.Macaw.Memory.LoadCommon as MML

-- | Heuristics about how large (in bytes) the sizes of PLT-related stub
-- functions are. See @Note [PLT stub names]@ for more information. These
-- heuristics are tailored to each architecture's dynamic relocations, which is
-- why this is parameterized by a @reloc@ type.
--
-- For more information about how to add your own value of type 'PLTStubInfo',
-- see @Note [Creating a new PLTStubInfo value]@.
data PLTStubInfo reloc = PLTStubInfo
  { pltFunSize :: Integer
    -- ^ The size of the @.plt@ function, which is the first function in the
    -- @.plt@ section in most cases.
  , pltStubSize :: Integer
    -- ^ The size of each PLT stub in the @.plt@ section.
  , pltGotStubSize :: Integer
    -- ^ The size of each PLT stub in the @.plt.got@ section. Note that not
    -- all architectures put stubs in a @.plt.got@ section, so it is
    -- permissible to implement this using 'error' on those architectures.
  }

-- | Match up names to PLT stub entries in a dynamically linked ELF binary.
--
-- Calls to functions in shared libraries are issued through PLT stubs. These
-- are short sequences included in the binary by the compiler that jump to the
-- *real* function implementation in the shared library via the Global Offset
-- Table. The GOT is populated by the dynamic loader.
--
-- See @Note [PLT stub names]@ for more details.
pltStubSymbols
  :: forall reloc w
   . ( w ~ EE.RelocationWidth reloc
     , DMM.MemWidth w
     , EE.IsRelocationType reloc
     )
  => PLTStubInfo reloc
     -- ^ Heuristics about how large PLT stubs should be.
  -> MML.LoadOptions
     -- ^ Options configuring how to load the address of each PLT stub.
  -> EE.ElfHeaderInfo w
     -- ^ The dynamically linked ELF binary.
  -> Map.Map (DMM.MemWord w) (EE.VersionedSymbol (EE.ElfWordType w))
pltStubSymbols pltStubInfo loadOptions ehi =
  EE.elfClassInstances elfClass $
  Map.fromList $ fromMaybe [] $ do
    vam <- EE.virtAddrMap elfBytes elfPhdrs

    dynBytes <- case filter (\p -> EE.phdrSegmentType p == EE.PT_DYNAMIC) elfPhdrs of
      [dynPhdr] -> return (EE.slice (EE.phdrFileRange dynPhdr) elfBytes)
      _         -> Nothing

    dynSec <- case EE.dynamicEntries (EE.elfData elf) elfClass dynBytes of
      Left _dynErr -> Nothing
      Right dynSec -> return dynSec

    vdefm <- case EE.dynVersionDefMap dynSec vam of
      Left _dynErr -> Nothing
      Right vm -> return vm

    vreqm <- case EE.dynVersionReqMap dynSec vam of
      Left _dynErr -> Nothing
      Right vm -> return vm

    let pltAddrs = case extractPltAddrs dynSec vam vdefm vreqm of
          Nothing -> []
          Just addrs -> addrs

    let pltGotAddrs = case extractPltGotAddrs dynSec vam vdefm vreqm of
          Nothing -> []
          Just addrs -> addrs

    return (pltAddrs ++ pltGotAddrs)
  where
    (_, elf) = EE.getElf ehi
    elfPhdrs = EE.headerPhdrs ehi
    elfBytes = EE.headerFileContents ehi
    elfClass = EE.elfClass elf

    pltStubAddress :: forall relOrRela
                    . EE.DynamicSection w
                   -> EE.VirtAddrMap w
                   -> EE.VersionDefMap
                   -> EE.VersionReqMap
                   -> (relOrRela reloc -> Word32)
                      -- ^ The function for extracting the index of a REL or
                      -- RELA relocation in the Global Offset Table
                   -> [EE.VersionedSymbol (EE.ElfWordType w)]
                      -- The list of PLT-related function symbols accumulated
                      -- so far
                   -> relOrRela reloc
                      -- ^ The REL or RELA relocation, from which we will find
                      -- the corresponding PLT stub
                   -> [EE.VersionedSymbol (EE.ElfWordType w)]
    pltStubAddress dynSec vam vdefm vreqm getRelSymIdx accum rel
      | Right entry <- EE.dynSymEntry dynSec vam vdefm vreqm (getRelSymIdx rel) =
          entry : accum
      | otherwise = accum

    -- Build an association list of PLT stub addresses and their corresponding
    -- function symbols.
    buildAssocList :: forall versym
                    . [(Integer, versym)]
                      -- ^ The PLT stub addresses (as raw Integers) and their
                      -- corresponding symbol names.
                   -> Integer
                      -- ^ The starting address of the section containing the PLT stubs
                   -> Integer
                      -- ^ The size of a PLT stub
                   -> [(DMM.MemWord w, versym)]
    buildAssocList nameRelaMap baseAddr stubSize =
      let loadOffset = toInteger $ fromMaybe 0 (MML.loadOffset loadOptions) in
      [ (DMM.memWord (fromInteger addr), versym)
      | (idx, versym) <- nameRelaMap
      , let addr = loadOffset + baseAddr + idx * stubSize
      ]

    -- Build an association list from addresses of stubs in the .plt section to
    -- their function names.
    extractPltAddrs :: Integral (EE.ElfWordType w)
                    => EE.DynamicSection w
                    -> EE.VirtAddrMap w
                    -> EE.VersionDefMap
                    -> EE.VersionReqMap
                    -> Maybe [(DMM.MemWord w, EE.VersionedSymbol (EE.ElfWordType w))]
    extractPltAddrs dynSec vam vdefm vreqm = do
      SomeRel rels getRelSymIdx <- case EE.dynPLTRel @reloc dynSec vam of
        Right (EE.PLTRela relas) -> return (SomeRel relas EE.relaSym)
        Right (EE.PLTRel rels) -> return (SomeRel rels EE.relSym)
        _ -> Nothing
      let revNameRelaMap = foldl' (pltStubAddress dynSec vam vdefm vreqm getRelSymIdx) [] rels
      let nameRelaMap = zip [0..] (reverse revNameRelaMap)
      pltSec <- listToMaybe (EE.findSectionByName (BSC.pack ".plt") elf)
      let pltBase = EE.elfSectionAddr pltSec
      let pltFunSz  = pltFunSize pltStubInfo
      let pltStubSz = pltStubSize pltStubInfo
      return $ buildAssocList nameRelaMap (pltFunSz + toInteger pltBase) pltStubSz

    -- Build an association list from addresses of stubs in the .plt.got section
    -- to their function names.
    extractPltGotAddrs :: Integral (EE.ElfWordType w)
                       => EE.DynamicSection w
                       -> EE.VirtAddrMap w
                       -> EE.VersionDefMap
                       -> EE.VersionReqMap
                       -> Maybe [(DMM.MemWord w, EE.VersionedSymbol (EE.ElfWordType w))]
    extractPltGotAddrs dynSec vam vdefm vreqm = do
      relsGot <- case EE.dynRelaEntries @reloc dynSec vam of
        Right relas -> return relas
        Left _ -> Nothing
      let revNameRelaMapGot = foldl' (pltStubAddress dynSec vam vdefm vreqm EE.relaSym) [] relsGot
      let nameRelaMapGot = zip [0..] (reverse revNameRelaMapGot)
      pltGotSec <- listToMaybe (EE.findSectionByName (BSC.pack ".plt.got") elf)
      let pltGotBase = EE.elfSectionAddr pltGotSec
      let pltGotStubSz = pltGotStubSize pltStubInfo
      return $ buildAssocList nameRelaMapGot (toInteger pltGotBase) pltGotStubSz

-- | A wrapper type that existentially closes over whether we are dealing with a
-- REL or RELA relocation. This makes it easier to extract and process both
-- relocation types at the same time.
data SomeRel reloc where
  SomeRel :: [relOrRela reloc] -> (relOrRela reloc -> Word32) -> SomeRel reloc

-- | A dummy relocation type that is used for architectures that do not yet have
-- a dynamic relocation type defined in @elf-edit@. The corresponding
-- 'EE.IsRelocationType' instance will simply error.
data NoRelocationType (w :: Nat) = NoRelocationType
  deriving Show

noRelocationTypeError :: a
noRelocationTypeError = error $
  "Attempting to use dynamic relocations on an architecture " ++
  "that has not yet been configured to use them."

-- | A dummy 'EE.IsRelocationType' instance that will simply error if used.
instance Show (EE.ElfWordType w) => EE.IsRelocationType (NoRelocationType w) where
  -- The particular choice of width doesn't matter here, but we do need /some/
  -- choice of Nat to make IsRelocationType's superclass instances work out.
  type RelocationWidth (NoRelocationType w) = w

  relaWidth = noRelocationTypeError
  toRelocType = noRelocationTypeError
  isRelative = noRelocationTypeError
  relocTargetBits = noRelocationTypeError

noPLTStubInfo :: String -> PLTStubInfo (NoRelocationType w)
noPLTStubInfo arch = error $
  "The " ++ arch ++
  " architecture has not yet been configured to support PLT stubs."

{-
Note [PLT stub names]
~~~~~~~~~~~~~~~~~~~~~
In a dynamically linked binary, the compiler issues calls to shared library
functions by jumping to a PLT stub. The PLT stub jumps to an address taken from
the Global Offset Table (GOT), which is populated by the dynamic loader based
on where the shared library is mapped into memory.

These PLT stubs are not inherently assigned names, but we would like to have
sensible names that we can simulate the functions of the same names in the
corresponding shared library.

PLT stubs do not have their own names in any symbol table. Instead, entries in
the Global Offset Table have names in the form of dynamic PLT relocations.  We
get those from elf-edit via the 'dynPLTRel' function. Note that these
relocations do not have their own directly associated names; instead, there is
a list of rela entries and a separate list of symbols. The list of rela entries
contains function relocations while the list of dynamic symbols ('dynSymEntry')
contains both function and object symbols. To align them, we must just discard
the non-function entries. We do this by checking if the current symbol entry is
of function type; if it is not, we just grab the next function symbol in the
list.

That step gives us names for global offset table entries, but *not* names for
PLT stubs. We rely on the fact that the list of PLT stubs is in the same order
as the list of global offset table entries. The previous step gives us the
*index* of each entry and a name for that entry. To get the name of the PLT
stub itself, we just compute the relevant offset from the base of the .plt
section. Each PLT stub is 16 bytes on most architectures. For example, on
x86_64 the address of the PLT stub of an entry is @addrOf(.plt) + 16 * idx@.

Ultimately, the approach above relies on the assumption that PLT stubs will
always be the same size in each binary on a particular architecture.
Unfortunately, this is not true in practice, as the exact size of a PLT stub
can vary depending on factors such as:

* What linker you use. For example, the `mold` linker produces PLT stubs that
  are 8 bytes large on x86-64 (instead of 16 bytes) by default. To override
  this, one must pass -Wl,-z,lazy to `mold`.

* Whether you compile with instrumentation of control-flow transfers. This
  is something that recent versions of Ubuntu use in their distribution of
  `gcc`, which has the side effect of producing PLT stubs that are larger
  than 16 bytes. To override this, one must pass `-fcf-protection=none` to
  `gcc`.

Getting this right in all cases would likely require doing a more detailed
analysis of the underlying machine code, which is what tools like `angr` do.
(See this comment in `angr`, which is very relevant to this discussion:
https://github.com/angr/cle/blob/4a7e4f7a6f1151f5587bf8bfa919da0064bd2449/cle/backends/elf/metaelf.py#L110-L116 )
For now, we settle for getting the "common-case" heuristics right.

Note [Creating a new PLTStubInfo value]
~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~
We factor out the heuristics used to compute the sizes of PLT-related stubs
into the PLTStubInfo data type. Currently, not all architectures have a
corresponding PLTStubInfo value, and it is possible that you will need to add
such a value for the architecture you are using. If that is the case, then you
can do so by following these steps. As a running example, we will trace through
the steps needed to define a PLTStubInfo value for x86-64:

1. Make sure that the @elf-edit@ library defines a dynamic relocation type for
   the architecture that you care about. For instance, @elf-edit@ provides an
   @X86_64_RelocationType@ for x86-64 in Data.ElfEdit.Relocations.X86_64, along
   with a corresponding IsRelocationType instance. The pltStubSymbols function
   makes use of this instance, so make sure to define it.

2. Next, obtain a C compiler for your architecture. In the case of x86-64, it
   should be relatively straightforward to download one from your package
   manager. For other architectures, the https://musl.cc website contains a
   wide variety of cross-compilers for different architectures.

3. Next, we need to see how large the sizes of PLT stubs are so that we can
   develop appropriate heuristics. One way to accomplish this is to use this
   C program as a smoke test:

     #include <stdlib.h>
     #include <unistd.h>
     #include <sys/types.h>

     int main(void) {
       void* (*m)(size_t) = &malloc;
       void* (*c)(size_t, size_t) = &calloc;

       int* x = malloc(sizeof(int));
       int* y = calloc(sizeof(int), 1);

       pid_t pid = getpid();
       pid_t ppid = getppid();

       return 0;
     }

   This directly invokes two functions defined in a shared library (libc), and
   it also invokes two shared library functions indirectly by way of function
   pointers. This provides a healthy combination of different ways to
   dynamically link against functions, which will be helpful for our heuristics.

   Compile this program like so:

     <path-to-c-compiler> -no-pie -fcf-protection=none test.c -o test.exe

   We pass `-no-pie` and `-fcf-protection=none` here to get the "common case"
   for how the compiler lays out its PLT-related address space. (Again, we
   are developing heuristics, and these heuristics aren't perfect.)

4. Now run `objdump` (which comes shipped with https://musl.cc binary
   distributions) to disassemble the test executable:

     <path-to-objdump> -d test.exe

   You will see output like this:

     test.exe:     file format elf64-x86-64


     Disassembly of section .init:

     0000000000401000 <_init>:
       401000:       50                      push   %rax
       401001:       58                      pop    %rax
       401002:       c3                      retq

     Disassembly of section .plt:

     0000000000401010 <.plt>:
       401010:       ff 35 f2 2f 00 00       pushq  0x2ff2(%rip)        # 404008 <_GLOBAL_OFFSET_TABLE_+0x8>
       401016:       ff 25 f4 2f 00 00       jmpq   *0x2ff4(%rip)        # 404010 <_GLOBAL_OFFSET_TABLE_+0x10>
       40101c:       0f 1f 40 00             nopl   0x0(%rax)

     0000000000401020 <getpid@plt>:
       401020:       ff 25 f2 2f 00 00       jmpq   *0x2ff2(%rip)        # 404018 <getpid>
       401026:       68 00 00 00 00          pushq  $0x0
       40102b:       e9 e0 ff ff ff          jmpq   401010 <.plt>

     0000000000401030 <getppid@plt>:
       401030:       ff 25 ea 2f 00 00       jmpq   *0x2fea(%rip)        # 404020 <getppid>
       401036:       68 01 00 00 00          pushq  $0x1
       40103b:       e9 d0 ff ff ff          jmpq   401010 <.plt>

     0000000000401040 <__libc_start_main@plt>:
       401040:       ff 25 e2 2f 00 00       jmpq   *0x2fe2(%rip)        # 404028 <__libc_start_main>
       401046:       68 02 00 00 00          pushq  $0x2
       40104b:       e9 c0 ff ff ff          jmpq   401010 <.plt>

     Disassembly of section .plt.got:

     0000000000401050 <__cxa_finalize@plt>:
       401050:       ff 25 82 2f 00 00       jmpq   *0x2f82(%rip)        # 403fd8 <__cxa_finalize>
       401056:       66 90                   xchg   %ax,%ax

     0000000000401058 <malloc@plt>:
       401058:       ff 25 82 2f 00 00       jmpq   *0x2f82(%rip)        # 403fe0 <malloc>
       40105e:       66 90                   xchg   %ax,%ax

     0000000000401060 <calloc@plt>:
       401060:       ff 25 82 2f 00 00       jmpq   *0x2f82(%rip)        # 403fe8 <calloc>
       401066:       66 90                   xchg   %ax,%ax

     Disassembly of section .text:

     ...

   We will be using the information above to compute the three values in the
   PLTStubInfo data constructor.

5. First, we need to compute pltFunSize, which is the size (in bytes) of the
   <.plt> function above. This is straightforward enough to do in GHCi:

     > 0x401020 - 0x401010
     16

   Here, 0x401010 is the address for <.plt>, and 0x401020 is the address of the
   <getpid@plt> stub that directly follows <.plt>. GHCi tells us that the
   difference is 16 bytes, so that is the value that we use for pltFunSize.

6. Second, we need to compute pltStubSize, which is the size of each stub in the
   .plt section. Each stub function's name ends with @plt, e.g., <getpid@plt>.
   We can again use GHCi to compute the size of <getpid@plt>:

     > 0x401030 - 0x401020
     16

7. Finally, we need to compute pltGotStubSize, which is the size of each stub in
   the .plt.got section. This is a special section that some architectures
   reserve for things like function pointers, such as &malloc and &calloc in
   the program above. GHCi tells us the size of <malloc@plt>:

     > 0x401060 - 0x401058
     8

   Note that not all architectures have .plt.got sections (e.g., AArch32).
   For these architectures, the pltStubSymbols function will never make use of
   the value of pltGotStubSize, so it is permissible to implement it using the
   `error` function.

Putting all of these together, we arrive at the definition of x86_64PLTStubInfo
in Data.Macaw.X86:

  x86_64PLTStubInfo :: PLTStubInfo X86_64_RelocationType
  x86_64PLTStubInfo = PLTStubInfo
    { pltFunSize     = 16
    , pltStubSize    = 16
    , pltGotStubSize = 8
    }
-}
