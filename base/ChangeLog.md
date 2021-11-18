# Revision history for macaw-base

## Next

### Features

### API Changes

- Architecture-specific block terminators can now contain macaw values

  This changed the type of the architecture extension block terminators from `ArchTermStmt ids` to `ArchTermStmt f` where `f ~ Value arch ids` at the macaw level.

- Architecture backends can now configure the block classification during the discovery phase

  The interface to configure block classification is exposed through the `ArchitectureInfo`. Note that clients that have not created their own `ArchitectureInfo` from scratch should be unaffected (which is the vast majority).

- The post-discovery AST types are now exported from `Data.Macaw.Discovery.ParsedContents`

  It is recommended that future references to these types be done through this module. They are re-exported from their original location (`Data.Macaw.Discovery.State`) for backwards compatibility. One day that is likely to change.

