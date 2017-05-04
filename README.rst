The macaw library implements architecture-independent binary code
discovery.  Support for specific architectures is provided by
implementing the semantics of that architecture.  The library is
written in terms of an abstract interface to memory, for which an ELF
backend is provided (via the elf-edit_ library).  The basic code
discovery is based on a variant of Value Set Analysis (VSA).

The most important user-facing abstractions are:

* The ``Memory`` type, defined in ``Data.Macaw.Memory``, which provides an abstract interface to an address space containing both code and data.
* The ``memoryForElfSegments`` function is a useful helper to produce a ``Memory`` from an ELF file.
* The ``cfgFromAddrs`` function, defined in ``Data.Macaw.Discovery``, which performs code discovery on a ``Memory`` given some initial parameters (semantics to use via ``ArchitectureInfo`` and some entry points.
* The ``DiscoveryInfo`` type, which is the result of ``cfgFromAddrs``; it contains a collection of ``DiscoveryFunInfo`` records, each of which represents a discovered function.  Every basic block is assigned to at least one function.

Architecture-specific code goes into separate libraries.  X86-specific code is in the macaw-x86 repo.

An abbreviated example of using macaw on an ELF file looks like::

  import qualified Data.Map as M

  import qualified Data.ElfEdit as E
  import qualified Data.Parameterized.Some as PU
  import qualified Data.Macaw.Architecture.Info as AI
  import qualified Data.Macaw.Memory as MM
  import qualified Data.Macaw.Memory.ElfLoader as MM
  import qualified Data.Macaw.Discovery as MD
  import qualified Data.Macaw.Discovery.Info as MD

  discoverCode :: E.Elf Word64 -> AI.ArchitectureInfo X86_64 -> (forall ids . MD.DiscoveryInfo X86_64 ids -> a) -> a
  discoverCode elf archInfo k =
    withMemory MM.Addr64 elf $ \mem ->
      let Just entryPoint = MM.absoluteAddrSegment mem (fromIntegral (E.elfEntry elf))
      in case MD.cfgFromAddrs archInfo mem M.empty [entryPoint] [] of
        PU.Some di -> k di

  withMemory :: forall w m a
              . (MM.MemWidth w, Integral (E.ElfWordType w))
             => MM.AddrWidthRepr w
             -> E.Elf (E.ElfWordType w)
             -> (MM.Memory w -> m a)
             -> m a
  withMemory relaWidth e k =
    case MM.memoryForElfSegments relaWidth e of
      Left err -> error (show err)
      Right (_sim, mem) -> k mem


In the callback, the ``DiscoveryInfo`` can be analyzed as desired.

Implementing support for an architecture is more involved and requires implementing an ``ArchitectureInfo``, which is defined in ``Data.Macaw.Architecture.Info``.  This structure contains architecture-specific information like:

* The pointer width
* A disassembler from bytes to abstract instructions
* ABI information regarding registers and calling conventions
* A transfer function for architecture-specific features not represented in the common IR

.. _elf-edit: https://github.com/GaloisInc/elf-edit
.. _flexdis86: https://github.com/GaloisInc/flexdis86
