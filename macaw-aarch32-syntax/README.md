# macaw-aarch32-syntax

This package provides concrete syntax for macaw-aarch32-symbolic types and
operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types and operations:

**Types**:

- `AArch32Regs`: the struct of all AArch32 registers

**Operations**:

- `get-reg :: AArch32Reg -> AArch32Regs -> t`: extract an x86 register
- `set-reg :: AArch32Reg -> t -> AArch32Regs -> AArch32Regs`: set an x86 register
- Registers:
  - `r0 :: AArch32Reg`
  - `r1 :: AArch32Reg`
  - `r2 :: AArch32Reg`
  - `r3 :: AArch32Reg`
  - `r4 :: AArch32Reg`
  - `r5 :: AArch32Reg`
  - `r6 :: AArch32Reg`
  - `r7 :: AArch32Reg`
  - `r8 :: AArch32Reg`
  - `r9 :: AArch32Reg`
  - `r10 :: AArch32Reg`
  - `r11 :: AArch32Reg`, AKA `fp`
  - `fp :: AArch32Reg`, AKA `r11`
  - `r12 :: AArch32Reg`, AKA `ip`
  - `ip :: AArch32Reg`, AKA `r12`
  - `r13 :: AArch32Reg`, AKA `sp`
  - `sp :: AArch32Reg`, AKA `r13`
  - `r14 :: AArch32Reg`, AKA `lr`
  - `lr :: AArch32Reg`, AKA `r14`
  - `v0 :: AArch32Reg`
  - `v1 :: AArch32Reg`
  - `v2 :: AArch32Reg`
  - `v3 :: AArch32Reg`
  - `v4 :: AArch32Reg`
  - `v5 :: AArch32Reg`
  - `v6 :: AArch32Reg`
  - `v7 :: AArch32Reg`
  - `v8 :: AArch32Reg`
  - `v9 :: AArch32Reg`
  - `v10 :: AArch32Reg`
  - `v11 :: AArch32Reg`
  - `v12 :: AArch32Reg`
  - `v13 :: AArch32Reg`
  - `v14 :: AArch32Reg`
  - `v15 :: AArch32Reg`
  - `v16 :: AArch32Reg`
  - `v17 :: AArch32Reg`
  - `v18 :: AArch32Reg`
  - `v19 :: AArch32Reg`
  - `v20 :: AArch32Reg`
  - `v21 :: AArch32Reg`
  - `v22 :: AArch32Reg`
  - `v23 :: AArch32Reg`
  - `v24 :: AArch32Reg`
  - `v25 :: AArch32Reg`
  - `v26 :: AArch32Reg`
  - `v27 :: AArch32Reg`
  - `v28 :: AArch32Reg`
  - `v29 :: AArch32Reg`
  - `v30 :: AArch32Reg`
  - `v31 :: AArch32Reg`

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
