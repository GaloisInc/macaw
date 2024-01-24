# Revision history for macaw-base

## Next

### Features

- `resolveElfContents`, as well as related functions in
  `Data.Macaw.Memory.ElfLoader`, now compute dynamic function symbols for
  non–position-independent executables. These were previously omitted due to
  an oversight in the implementation.

- Add support for PPC32 and PPC64 relocations in `Data.Macaw.Memory.ElfLoader`.

### API Changes

- Architecture-specific block terminators can now contain macaw values

  This changed the type of the architecture extension block terminators from `ArchTermStmt ids` to `ArchTermStmt f` where `f ~ Value arch ids` at the macaw level.

- Architecture backends can now configure the block classification during the discovery phase

  The interface to configure block classification is exposed through the `ArchitectureInfo`. Note that clients that have not created their own `ArchitectureInfo` from scratch should be unaffected (which is the vast majority).

- The post-discovery AST types are now exported from `Data.Macaw.Discovery.ParsedContents`

  It is recommended that future references to these types be done through this module. They are re-exported from their original location (`Data.Macaw.Discovery.State`) for backwards compatibility. One day that is likely to change.

- The `DynamicSymbolTable` constructor of `Data.Macaw.Memory.ElfLoader`'s
  `SymbolTable` data type now has an additional `VersionDefMap` field, which is
  needed for finding versioning information in some cases.

- The `Hashable` and `HashableF` instances for `App f` now require
  `TestEquality f` constraints. (This is needed to support `hashable-1.4.*`,
  which adds `Eq` as a superclass to `Hashable`.)
