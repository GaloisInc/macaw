{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StandaloneDeriving #-}

-- | Functionality for computing the names and addresses of PLT stub functions
-- in a dynamically linked ELF binary.
--
-- Note that the API in this library is somewhat experimental, and as we further
-- develop the underlying approach (see @Note [Dynamic lookup scope]@), we may
-- need to change the API accordingly.
module Data.Macaw.Memory.ElfLoader.DynamicDependencies
  ( loadDynamicDependencies
  , parseDynNeeded
  , DynamicLoadingError(..)
  ) where

import qualified Control.Exception as X
import qualified Control.Monad.Catch as CMC
import qualified Data.ByteString as BS
import qualified Data.ByteString.UTF8 as UTF8
import qualified Data.ElfEdit as EE
import qualified Data.Set as Set
import qualified Data.Sequence as Seq
import qualified Data.Type.Equality as DTE
import qualified Prettyprinter as PP
import qualified System.Directory as SD
import qualified System.FilePath as SF

-- | Given a binary, load all of the shared libraries that it transitively
-- depends on, returning the order in which they were encountered in a
-- breadth-first search. Returning them in this order is important since we
-- rely on the assumption that the binaries are in the same order as the global
-- lookup scope. See @Note [Dynamic lookup scope]@.
--
-- This function makes a couple of simplifying assumptions about how shared
-- libraries work that are not true in general:
--
-- * All of the shared libraries that the main binary depends on are located in
--   a single directory.
--
-- * None of the binaries use @dlopen@, which can load additional shared
--   libraries at runtime.
loadDynamicDependencies ::
     forall w
   . EE.ElfMachine
  -- ^ The architecture of the main binary (x86-64, AArch32, etc.)
  -> EE.ElfClass w
  -- ^ Whether the main binary is 32-bit or 64-bit
  -> FilePath
  -- ^ The directory in which the shared libraries live
  -> EE.ElfHeaderInfo w
  -- ^ The main binary's ELF header info
  -> FilePath
  -- ^ The main binary's path
  -> IO [(EE.ElfHeaderInfo w, FilePath)]
  -- ^ The shared libraries in order of global lookup scope, paired with their
  -- file paths
loadDynamicDependencies expectedHeaderMachine expectedHeaderClass
                        sharedObjectDir mainBinaryEHI mainBinaryPath =
   -- First, parse the DT_NEEDED entries of the main binary.
   case parseDynNeeded mainBinaryEHI mainBinaryPath of
     -- If this returns Nothing, the binary isn't dynamically linked.
     -- We return an empty list of shared libraries in this case.
     Nothing -> pure []
     -- Otherwise, proceed with a breadth-first search of the DT_NEEDED entries
     -- in each of the shared libraries.
     Just dynNeededs -> do
       dynNeededs' <- either CMC.throwM pure dynNeededs
       go Set.empty $ Seq.fromList dynNeededs'
  where
    -- The main loop in the breadth-first search.
    go ::
      Set.Set BS.ByteString ->
      -- ^ The set of shared libraries that we have already loaded.
      Seq.Seq BS.ByteString ->
      -- ^ The queue of @DT_NEEDED@ entries that need to be processed.
      IO [(EE.ElfHeaderInfo w, FilePath)]
    go sosSeenSoFar dynQueue =
      -- Dequeue the next DT_NEEDED entry on the queue.
      case Seq.viewl dynQueue of
        Seq.EmptyL -> pure []
        dynNext Seq.:< dynRest
          |  -- If we have already loaded this shared library, skip it and
             -- process the rest of the queue.
             dynNext `Set.member` sosSeenSoFar
          -> go sosSeenSoFar dynRest
          |  otherwise
          -> do let dynNextFP = UTF8.toString dynNext
                let fullPath = sharedObjectDir SF.</> dynNextFP
                exists <- SD.doesFileExist fullPath
                -- We only attempt to load a shared library if it exists on the
                -- user-specified path. Otherwise, we skip it and process the
                -- rest of the queue.
                --
                -- This is a design choice, as we could just as well throw an
                -- error here if the shared library does not exist. We opt to
                -- be somewhat lenient here because it's common for binaries to
                -- link against shared libraries that aren't reached from most
                -- code paths, such as libc. We want to be able to analyze these
                -- code paths without requiring the user to hunt down every last
                -- shared library that the binary could potentially use.
                if exists
                  then do
                    -- Read the shared library from disk and load it.
                    soBytes <- BS.readFile fullPath
                    so <- loadSharedObject dynNextFP soBytes
                    case parseDynNeeded so dynNextFP of
                      -- By definition, each of the shared libraries
                      -- should be dynamically linked. If they're not,
                      -- something very fishy is going on, so throw an
                      -- error.
                      Nothing -> CMC.throwM $ ElfNonDynamicSharedLib dynNextFP
                      -- Otherwise, return the loaded shared library and
                      -- proceed. In the process of doing so, we add the
                      -- shared library to the set of already loaded
                      -- libraries and add the DT_NEEDED entries from the
                      -- shared library to the back of the queue.
                      Just dynNeededs -> do
                        dynNeededs' <- either CMC.throwM pure dynNeededs
                        sos <- go (Set.insert dynNext sosSeenSoFar)
                                  (dynRest <> Seq.fromList dynNeededs')
                        pure ((so, dynNextFP):sos)
                   else go sosSeenSoFar dynRest

    -- Load a shared library from bytes.
    loadSharedObject ::
      FilePath ->
      -- ^ The path to the shared library
      BS.ByteString ->
      -- ^ The contents of the shared library
      IO (EE.ElfHeaderInfo w)
    loadSharedObject soName soBytes =
      case EE.decodeElfHeaderInfo soBytes of
        Right (EE.SomeElf ehi) -> do
          let hdr = EE.header ehi
          let actualHeaderClass = EE.headerClass hdr
          let actualHeaderMachine = EE.headerMachine hdr

          if actualHeaderMachine == expectedHeaderMachine
          then
            case DTE.testEquality actualHeaderClass expectedHeaderClass of
              Just DTE.Refl -> pure ehi
              _ -> CMC.throwM $ SoMismatchedElfClass actualHeaderClass
                                                     expectedHeaderClass
          else CMC.throwM $ SoMismatchedElfMachine actualHeaderMachine
                                                   expectedHeaderMachine
        Left _ -> CMC.throwM $ NonElfBinaryFormat soName

-- | Get values of @DT_NEEDED@ entries in an ELF file. If this is not a dynamic
-- executable, then @Nothing@ is returned.
parseDynNeeded ::
  EE.ElfHeaderInfo w ->
  FilePath ->
  -- ^ The path to the ELF file
  Maybe (Either DynamicLoadingError [BS.ByteString])
parseDynNeeded elfHeaderInfo elfFP = EE.elfClassInstances elfClass $
  case filter (\p -> EE.phdrSegmentType p == EE.PT_DYNAMIC) elfPhdrs of
    [dynPhdr] -> Just $
      let dynContents = EE.slice (EE.phdrFileRange dynPhdr) elfBytes
      in case EE.dynamicEntries (EE.headerData elfHeader) elfClass dynContents of
           Left dynError ->
             Left $ ElfDynamicParseError elfFP dynError
           Right dynSection -> do
             case EE.virtAddrMap elfBytes elfPhdrs of
               Nothing -> do
                 Left $ ElfVirtualAddressMapError elfFP
               Just phdrs ->
                 case EE.dynNeeded dynSection phdrs of
                   Left errMsg -> Left $ ElfDynamicNeededError elfFP errMsg
                   Right deps -> Right deps
    [] -> Nothing
    _  -> Just $ Left $ ElfMultipleDynamicHeaders elfFP
  where
    elfHeader = EE.header elfHeaderInfo
    elfPhdrs = EE.headerPhdrs elfHeaderInfo
    elfBytes = EE.headerFileContents elfHeaderInfo
    elfClass = EE.headerClass elfHeader

data DynamicLoadingError where
  -- | Encountered a non-ELF binary format, which is not supported.
  NonElfBinaryFormat ::
       FilePath
    -> DynamicLoadingError

  -- | Encountered an error when parsing a dynamic section in an ELF binary.
  ElfDynamicParseError ::
       FilePath
    -> EE.DynamicError
    -> DynamicLoadingError

  -- | Encountered an error when parsing the @DT_NEEDED@ entries in a dynamic
  -- ELF binary.
  ElfDynamicNeededError ::
       FilePath
    -> String
    -> DynamicLoadingError

  -- | Could not constuct a virtual address map for an ELF binary.
  ElfVirtualAddressMapError ::
       FilePath
    -> DynamicLoadingError

  -- | Encountered multiple @PT_DYNAMIC@ program headers when parsing an ELF
  -- binary.
  ElfMultipleDynamicHeaders ::
       FilePath
    -> DynamicLoadingError

  -- | Encountered a shared library that is not dynamically linked.
  ElfNonDynamicSharedLib ::
       FilePath
    -> DynamicLoadingError

  -- | A provided shared object had a different ELF machine value than the main
  -- binary. The first argument is the 'EE.ElfMachine' for the shared object
  -- and the second argument is the 'EE.ElfMachine' for the main binary.
  SoMismatchedElfMachine ::
       EE.ElfMachine
    -> EE.ElfMachine
    -> DynamicLoadingError

  -- | A provided shared object had a different ELF class value than the main
  -- binary. The first argument is the 'EE.ElfClass' for the shared object
  -- and the second argument is the 'EE.ElfClass' for the main binary.
  SoMismatchedElfClass ::
       EE.ElfClass w
    -> EE.ElfClass w'
    -> DynamicLoadingError

deriving instance Show DynamicLoadingError

instance X.Exception DynamicLoadingError where
  displayException = show . PP.pretty

instance PP.Pretty DynamicLoadingError where
  pretty e =
    case e of
      NonElfBinaryFormat p ->
        "Unsupported, non-ELF binary format for file" PP.<+>
        PP.dquotes (PP.pretty p)

      ElfDynamicParseError fp dynErr ->
        PP.vcat
          [ PP.viaShow dynErr
          , "In the file:" PP.<+> PP.pretty fp
          ]
      ElfVirtualAddressMapError fp ->
        PP.vcat
          [ "Could not construct virtual address map"
          , "In the file:" PP.<+> PP.pretty fp
          ]
      ElfDynamicNeededError fp errMsg ->
        PP.vcat
          [ PP.pretty errMsg
          , "In the file:" PP.<+> PP.pretty fp
          ]
      ElfMultipleDynamicHeaders fp ->
        PP.vcat
          [ "Encountered multiple PT_DYNAMIC program headers"
          , "In the file:" PP.<+> PP.pretty fp
          ]
      ElfNonDynamicSharedLib fp ->
        "The shared library" PP.<+> PP.pretty fp PP.<+>
        "is not dynamically linked"
      SoMismatchedElfMachine soMachine mainMachine ->
        PP.vcat
          [ "A shared object has a different ELF machine value than the main binary."
          , "Shared object has machine " PP.<+> PP.viaShow soMachine PP.<+>
            "and main binary has machine " PP.<+> PP.viaShow mainMachine
          ]
      SoMismatchedElfClass soClass mainClass ->
        PP.vcat
          [ "A shared object has a different ELF class value than the main binary."
          , "Shared object has class " PP.<+> PP.viaShow soClass PP.<+>
            "and main binary has class " PP.<+> PP.viaShow mainClass
          ]

{-
Note [Dynamic lookup scope]
~~~~~~~~~~~~~~~~~~~~~~~~~~~
When looking up a dynamically linked function, which shared libraries should be
searched, and in which order? Answering this question precisely is tricky.

Section 1.5.4 of "How to Write Shared Libraries" on lookup scopes
(https://www.cs.dartmouth.edu/~sergey/cs258/ABI/UlrichDrepper-How-To-Write-Shared-Libraries.pdf)
offers a very detailed answer, although it is quite involved since it tries to
specify the behavior of `dlopen`. macaw needs to care about lookup scopes to
some degree, since it affects the semantics of dynamically linked programs, but
for now we prefer to pretend that `dlopen` isn't a thing. To borrow section
1.5.4's jargon, that means that we need to simulate the /global/ lookup scope,
but not local lookup scopes.

When macaw loads shared libraries, it returns them in the order dictated by the
global scope. An ELF binary's direct shared library dependencies are contained
in the DT_NEEDED entries, so to determine the global scope, we perform a
breadth-first search over the DT_NEEDED entries of the main binary and the
entries of the libraries that it depends on. See `loadDynamicDependencies` for
the full details.

Having the loaded binaries be in the same order as the global scope becomes
important when resolving dynamic function symbols. It's possible for two
binaries to define different functions of the same name. For example, imagine
this scenario:

  // a.c
  char f() { return 'a'; }

  // b.c
  char f() { return 'b'; }

  // main.c
  char f();
  int main() { printf("%c\n", f()); }

Suppose a.c and b.c are compiled to shared libraries liba.so and libb.so,
respectively, and that main.c is compiled to a main.exe binary that links
against both liba and libb. What will main.exe print when invoked? The answer
depends on the order of DT_NEEDED entries in main.exe, which in turn depends on
the order in which main.exe was linked against liba and libb when compiled. If
it was compiled like so:

  gcc -L. -la -lb main.c -o main.exe

Then the global scope will be:

  [main.exe, liba.so, libb.so]

And looking up f() will find liba.so first, causing 'a' to be printed. By a
similar token, if main.exe is compiled with `-lb -la` instead, then main.exe
would print 'b'.

This search order is implemented on the macaw-symbolic side in
Data.Macaw.Symbolic.Testing.runDiscovery, which puts all of the dynamic symbols
in a binary into a single Map. The symbols will be inserted into the map in the
order the binaries appear in the global scope, and in the event that we
encounter a symbol that has already been inserted into the map, we will always
prefer the already-inserted symbol, as that appears first in the global scope.

It's worth emphasizing that this implementation fundamentally relies on the
absence of dlopen. If we need to model dlopen in the future, we will have to
pick a more sophisticated implementation approach.
-}
