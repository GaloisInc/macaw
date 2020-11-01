# Overview

This package provides support in macaw for the 32 bit ARM architecture (both the ARM and Thumb encodings). The semantics are derived from the official ARM semantics (encoded in ASL and processed by the asl-translator Haskell package).

## Limitations

- Currently, this package does not support vector instructions. The semantics are available but they are disabled by default due to the increased compile times for the complex vector instruction semantics. They can be modified on a per-instruction basis via the `isUninterpretedOpcode` predicate in `Data.Macaw.ARM.Arch`.

# Quirks

- Thumb functions discovered by macaw have the low bit of their address set. This is an artifact of the Thumb calling convention, which indicates mode switches by setting the low bit of the jump address.  The reflection of this in the recovered function is not quite correct: disassembling from the address with the low bit set would actually yield the wrong results. This is not very important for most uses of macaw, but should be kept in mind when processing discovered Thumb functions.  Fixing this is possible but potentially fairly invasive.
