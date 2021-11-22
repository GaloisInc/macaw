# Revision history for macaw-symbolic

## Next

### Features

### API Changes

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
