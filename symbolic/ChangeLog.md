# Revision history for macaw-symbolic

## Next

### Features

### API Changes

- The `newGlobalMemory` and `newGlobalMemoryWith` functions now requires that `sym ~ ExprBuilder` due to some optimizations in populating the initial memory contents of large binaries

- The types of various functions, such as `macawExtensions`, are now parametric
  over the `personality` type variable instead of restricting it to
  `MacawSimulatorState sym`. A consequence of this change is that the
  `MacawArchEvalFn`, `LookupFunctionHandle`, and `LookupSyscallHandle` data
  types now have an additional `personality` type variable. If you don't care
  about this type variable, it is usually fine to leave it polymorphic.
  Alternatively, one can instantiate it to `MacawSimulatorState sym` to
  restore the old behavior.

- `Data.Macaw.Symbolic.MemOps.GlobalMap` has changed from a `type`
  synonym to a `newtype`, and its type has changed somewhat.

- The type of `crucGenArchTermStmt` has changed

  It gained a parameter of type `Maybe (Label c)` where `Label` comes from Crucible. This enables architecture-specific terminators to add custom control flow, including fallthrough behavior.

- `Data.Macaw.Symbolic.Backend` now exports some additional combinators

  These enable some more sophisticated translations in architecture-specific backends.
   - `appAtom`
   - `addTermStmt`
   - `createRegStruct`
   - `setMachineRegs`
   - `addExtraBlock`
   - `freshValueIndex`

- The following functions now have a `?memOpts :: MemOptions` constraint:
  - `Data.Macaw.Symbolic.Memory.newGlobalMemory`
  - `Data.Macaw.Symbolic.MemOps.{doWriteMem,doCondWriteMem}`

- The type of `populateRelocation` has gained three additional arguments—the
  `Memory`, `MemSegment`, and `MemAddr` corresponding to the relocation—to
  more easily facilitate computing the address of the relocation.

- `Data.Macaw.Symbolic.Testing` has made some API changes to support simulating
   shared libraries:
   - `runDiscovery` now returns a `BinariesInfo` value, which contains the code
     discovery state for both a main binary as well as any shared libraries that
     it depends on.
   - `runDiscovery` now requires the `FilePath` of the main binary as an
     argument, as well as a `PLTStubInfo` argument for determining where to look
     for PLT stubs in dynamically linked binaries. (See
     `Data.Macaw.Memory.ElfLoader.PLTStubs` in `macaw-base` for more information
     about `PLTStubInfo`s.)
   - `simulateAndVerify` has removed its `Memory` and `DiscoveryState` arguments
     in favor of a single `BinariesInfo` argument.

### Behavioral Changes

- Redundant pointer validity checks have been removed from `doReadMem`, `doCondReadMem`, `doWriteMem`, and `doCondWriteMem`; this should be mostly invisible to library clients unless they rely on goal counts or goal numbers
