# macaw-ppc-syntax

This package provides concrete syntax for macaw-ppc-symbolic types and
operations.

Concretely, it implements `ParserHooks` for use with [`crucible-syntax`][syn].
Note that we provide separate `ParserHooks` for PPC32 (32-bit PowerPC) and PPC64
(64-bit PowerPC), as the register types are separate in each variant of PowerPC.
Nevertheless, many operations work over both PPC32 and PPC64 alike.

The `ParserHooks` support the following types and operations:

**Types**:

- `PPC32Regs`: the struct of all PPC32 registers (not available on PPC64)
- `PPC64Regs`: the struct of all PPC64 registers (not available on PPC32)

**Operations**:

- `get-reg :: PPC{32,64}Reg -> PPC{32,64}Regs -> t`: extract a PowerPC register
- `set-reg :: PPC{32,64}Reg -> t -> PPC{32,64}Regs -> PPC{32,64}Regs`: set an PowerPC register
- Registers:
  - `ip :: PPC{32,64}Reg`
  - `lnk :: PPC{32,64}Reg`
  - `ctr :: PPC{32,64}Reg`
  - `xer :: PPC{32,64}Reg`
  - `cr :: PPC{32,64}Reg`
  - `fpscr :: PPC{32,64}Reg`
  - `vscr :: PPC{32,64}Reg`
  - `r0 :: PPC{32,64}Reg`
  - `r1 :: PPC{32,64}Reg`
  - `r2 :: PPC{32,64}Reg`
  - `r3 :: PPC{32,64}Reg`
  - `r4 :: PPC{32,64}Reg`
  - `r5 :: PPC{32,64}Reg`
  - `r6 :: PPC{32,64}Reg`
  - `r7 :: PPC{32,64}Reg`
  - `r8 :: PPC{32,64}Reg`
  - `r9 :: PPC{32,64}Reg`
  - `r10 :: PPC{32,64}Reg`
  - `r11 :: PPC{32,64}Reg`
  - `r12 :: PPC{32,64}Reg`
  - `r13 :: PPC{32,64}Reg`
  - `r14 :: PPC{32,64}Reg`
  - `r15 :: PPC{32,64}Reg`
  - `r16 :: PPC{32,64}Reg`
  - `r17 :: PPC{32,64}Reg`
  - `r18 :: PPC{32,64}Reg`
  - `r19 :: PPC{32,64}Reg`
  - `r20 :: PPC{32,64}Reg`
  - `r21 :: PPC{32,64}Reg`
  - `r22 :: PPC{32,64}Reg`
  - `r23 :: PPC{32,64}Reg`
  - `r24 :: PPC{32,64}Reg`
  - `r25 :: PPC{32,64}Reg`
  - `r26 :: PPC{32,64}Reg`
  - `r27 :: PPC{32,64}Reg`
  - `r28 :: PPC{32,64}Reg`
  - `r29 :: PPC{32,64}Reg`
  - `r30 :: PPC{32,64}Reg`
  - `r31 :: PPC{32,64}Reg`
  - `f0 :: PPC{32,64}Reg`
  - `f1 :: PPC{32,64}Reg`
  - `f2 :: PPC{32,64}Reg`
  - `f3 :: PPC{32,64}Reg`
  - `f4 :: PPC{32,64}Reg`
  - `f5 :: PPC{32,64}Reg`
  - `f6 :: PPC{32,64}Reg`
  - `f7 :: PPC{32,64}Reg`
  - `f8 :: PPC{32,64}Reg`
  - `f9 :: PPC{32,64}Reg`
  - `f10 :: PPC{32,64}Reg`
  - `f11 :: PPC{32,64}Reg`
  - `f12 :: PPC{32,64}Reg`
  - `f13 :: PPC{32,64}Reg`
  - `f14 :: PPC{32,64}Reg`
  - `f15 :: PPC{32,64}Reg`
  - `f16 :: PPC{32,64}Reg`
  - `f17 :: PPC{32,64}Reg`
  - `f18 :: PPC{32,64}Reg`
  - `f19 :: PPC{32,64}Reg`
  - `f20 :: PPC{32,64}Reg`
  - `f21 :: PPC{32,64}Reg`
  - `f22 :: PPC{32,64}Reg`
  - `f23 :: PPC{32,64}Reg`
  - `f24 :: PPC{32,64}Reg`
  - `f25 :: PPC{32,64}Reg`
  - `f26 :: PPC{32,64}Reg`
  - `f27 :: PPC{32,64}Reg`
  - `f28 :: PPC{32,64}Reg`
  - `f29 :: PPC{32,64}Reg`
  - `f30 :: PPC{32,64}Reg`
  - `f31 :: PPC{32,64}Reg`

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
