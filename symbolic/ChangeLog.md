# Revision history for macaw-symbolic

## Next

### Features

### API Changes

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

- `Data.Macaw.Symbolic.Memory.newGlobalMemory` now has a `?memOpts :: MemOptions` constraint.
