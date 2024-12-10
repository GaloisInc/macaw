# macaw-riscv-syntax

This package provides concrete syntax for macaw-riscv-symbolic types and
operations.

Concretely, it implements `ParserHooks` for use with [`crucible-syntax`][syn].
Note that we provide separate `ParserHooks` for RISCV32 (32-bit RISC-V) and
RISCV64 (64-bit RISC-V), as the register types are separate in each variant of
RISC-V. Nevertheless, many operations work over both RISCV32 and RISCV64 alike.

The `ParserHooks` support the following types and operations:

**Types**:

- `RISCV32Regs`: the struct of all RISCV32 registers (not available on RISCV64)
- `RISCV64Regs`: the struct of all RISCV64 registers (not available on RISCV32)

**Operations**:

- `get-reg :: RISCV{32,64}Reg -> RISCV{32,64}Regs -> t`: extract a RISC-V register
- `set-reg :: RISCV{32,64}Reg -> t -> RISCV{32,64}Regs -> RISCV{32,64}Regs`: set a RISC-V register
- Registers:
  - `pc :: RISCV{32,64}Reg`
  - `ra :: RISCV{32,64}Reg`, AKA `x1`
  - `sp :: RISCV{32,64}Reg`, AKA `x2`
  - `gp :: RISCV{32,64}Reg`, AKA `x3`
  - `tp :: RISCV{32,64}Reg`, AKA `x4`
  - `t0 :: RISCV{32,64}Reg`, AKA `x5`
  - `t1 :: RISCV{32,64}Reg`, AKA `x6`
  - `t2 :: RISCV{32,64}Reg`, AKA `x7`
  - `s0 :: RISCV{32,64}Reg`, AKA `x8`
  - `s1 :: RISCV{32,64}Reg`, AKA `x9`
  - `a0 :: RISCV{32,64}Reg`, AKA `x10`
  - `a1 :: RISCV{32,64}Reg`, AKA `x11`
  - `a2 :: RISCV{32,64}Reg`, AKA `x12`
  - `a3 :: RISCV{32,64}Reg`, AKA `x13`
  - `a4 :: RISCV{32,64}Reg`, AKA `x14`
  - `a5 :: RISCV{32,64}Reg`, AKA `x15`
  - `a6 :: RISCV{32,64}Reg`, AKA `x16`
  - `a7 :: RISCV{32,64}Reg`, AKA `x17`
  - `s2 :: RISCV{32,64}Reg`, AKA `x18`
  - `s3 :: RISCV{32,64}Reg`, AKA `x19`
  - `s4 :: RISCV{32,64}Reg`, AKA `x20`
  - `s5 :: RISCV{32,64}Reg`, AKA `x21`
  - `s6 :: RISCV{32,64}Reg`, AKA `x22`
  - `s7 :: RISCV{32,64}Reg`, AKA `x23`
  - `s8 :: RISCV{32,64}Reg`, AKA `x24`
  - `s9 :: RISCV{32,64}Reg`, AKA `x25`
  - `s10 :: RISCV{32,64}Reg`, AKA `x26`
  - `s11 :: RISCV{32,64}Reg`, AKA `x27`
  - `t3 :: RISCV{32,64}Reg`, AKA `x29`
  - `t4 :: RISCV{32,64}Reg`, AKA `x29`
  - `t5 :: RISCV{32,64}Reg`, AKA `x30`
  - `t6 :: RISCV{32,64}Reg`, AKA `x31`
  - `x1 :: RISCV{32,64}Reg`, AKA `ra`
  - `x2 :: RISCV{32,64}Reg`, AKA `sp`
  - `x3 :: RISCV{32,64}Reg`, AKA `gp`
  - `x4 :: RISCV{32,64}Reg`, AKA `tp`
  - `x5 :: RISCV{32,64}Reg`, AKA `t0`
  - `x6 :: RISCV{32,64}Reg`, AKA `t1`
  - `x7 :: RISCV{32,64}Reg`, AKA `t2`
  - `x8 :: RISCV{32,64}Reg`, AKA `s0`
  - `x9 :: RISCV{32,64}Reg`, AKA `s1`
  - `x10 :: RISCV{32,64}Reg`, AKA `a0`
  - `x11 :: RISCV{32,64}Reg`, AKA `a1`
  - `x12 :: RISCV{32,64}Reg`, AKA `a2`
  - `x13 :: RISCV{32,64}Reg`, AKA `a3`
  - `x14 :: RISCV{32,64}Reg`, AKA `a4`
  - `x15 :: RISCV{32,64}Reg`, AKA `a5`
  - `x16 :: RISCV{32,64}Reg`, AKA `a6`
  - `x17 :: RISCV{32,64}Reg`, AKA `a7`
  - `x18 :: RISCV{32,64}Reg`, AKA `s2`
  - `x19 :: RISCV{32,64}Reg`, AKA `s3`
  - `x20 :: RISCV{32,64}Reg`, AKA `s4`
  - `x21 :: RISCV{32,64}Reg`, AKA `s5`
  - `x22 :: RISCV{32,64}Reg`, AKA `s6`
  - `x23 :: RISCV{32,64}Reg`, AKA `s7`
  - `x24 :: RISCV{32,64}Reg`, AKA `s8`
  - `x25 :: RISCV{32,64}Reg`, AKA `s9`
  - `x26 :: RISCV{32,64}Reg`, AKA `s10`
  - `x27 :: RISCV{32,64}Reg`, AKA `s11`
  - `x28 :: RISCV{32,64}Reg`, AKA `t3`
  - `x29 :: RISCV{32,64}Reg`, AKA `t4`
  - `x30 :: RISCV{32,64}Reg`, AKA `t5`
  - `x31 :: RISCV{32,64}Reg`, AKA `t6`
  - `ft0 :: RISCV{32,64}Reg`, AKA `f0`
  - `ft1 :: RISCV{32,64}Reg`, AKA `f1`
  - `ft2 :: RISCV{32,64}Reg`, AKA `f2`
  - `ft3 :: RISCV{32,64}Reg`, AKA `f3`
  - `ft4 :: RISCV{32,64}Reg`, AKA `f4`
  - `ft5 :: RISCV{32,64}Reg`, AKA `f5`
  - `ft6 :: RISCV{32,64}Reg`, AKA `f6`
  - `ft7 :: RISCV{32,64}Reg`, AKA `f7`
  - `fs0 :: RISCV{32,64}Reg`, AKA `f8`
  - `fs1 :: RISCV{32,64}Reg`, AKA `f9`
  - `fa0 :: RISCV{32,64}Reg`, AKA `f10`
  - `fa1 :: RISCV{32,64}Reg`, AKA `f11`
  - `fa2 :: RISCV{32,64}Reg`, AKA `f12`
  - `fa3 :: RISCV{32,64}Reg`, AKA `f13`
  - `fa4 :: RISCV{32,64}Reg`, AKA `f14`
  - `fa5 :: RISCV{32,64}Reg`, AKA `f15`
  - `fa6 :: RISCV{32,64}Reg`, AKA `f16`
  - `fa7 :: RISCV{32,64}Reg`, AKA `f17`
  - `fs2 :: RISCV{32,64}Reg`, AKA `f18`
  - `fs3 :: RISCV{32,64}Reg`, AKA `f19`
  - `fs4 :: RISCV{32,64}Reg`, AKA `f2`
  - `fs5 :: RISCV{32,64}Reg`, AKA `f21`
  - `fs6 :: RISCV{32,64}Reg`, AKA `f22`
  - `fs7 :: RISCV{32,64}Reg`, AKA `f23`
  - `fs8 :: RISCV{32,64}Reg`, AKA `f24`
  - `fs9 :: RISCV{32,64}Reg`, AKA `f25`
  - `fs10 :: RISCV{32,64}Reg`, AKA `f26`
  - `fs11 :: RISCV{32,64}Reg`, AKA `f27`
  - `ft8 :: RISCV{32,64}Reg`, AKA `f28`
  - `ft9 :: RISCV{32,64}Reg`, AKA `f29`
  - `ft10 :: RISCV{32,64}Reg`, AKA `f30`
  - `ft11 :: RISCV{32,64}Reg`, AKA `f31`
  - `f0 :: RISCV{32,64}Reg`, AKA `ft0`
  - `f1 :: RISCV{32,64}Reg`, AKA `ft1`
  - `f2 :: RISCV{32,64}Reg`, AKA `ft2`
  - `f3 :: RISCV{32,64}Reg`, AKA `ft3`
  - `f4 :: RISCV{32,64}Reg`, AKA `ft4`
  - `f5 :: RISCV{32,64}Reg`, AKA `ft5`
  - `f6 :: RISCV{32,64}Reg`, AKA `ft6`
  - `f7 :: RISCV{32,64}Reg`, AKA `ft7`
  - `f8 :: RISCV{32,64}Reg`, AKA `fs0`
  - `f9 :: RISCV{32,64}Reg`, AKA `fs1`
  - `f10 :: RISCV{32,64}Reg`, AKA `fa0`
  - `f11 :: RISCV{32,64}Reg`, AKA `fa1`
  - `f12 :: RISCV{32,64}Reg`, AKA `fa2`
  - `f13 :: RISCV{32,64}Reg`, AKA `fa3`
  - `f14 :: RISCV{32,64}Reg`, AKA `fa4`
  - `f15 :: RISCV{32,64}Reg`, AKA `fa5`
  - `f16 :: RISCV{32,64}Reg`, AKA `fa6`
  - `f17 :: RISCV{32,64}Reg`, AKA `fa7`
  - `f18 :: RISCV{32,64}Reg`, AKA `fs2`
  - `f19 :: RISCV{32,64}Reg`, AKA `fs3`
  - `f20 :: RISCV{32,64}Reg`, AKA `fs4`
  - `f21 :: RISCV{32,64}Reg`, AKA `fs5`
  - `f22 :: RISCV{32,64}Reg`, AKA `fs6`
  - `f23 :: RISCV{32,64}Reg`, AKA `fs7`
  - `f24 :: RISCV{32,64}Reg`, AKA `fs8`
  - `f25 :: RISCV{32,64}Reg`, AKA `fs9`
  - `f26 :: RISCV{32,64}Reg`, AKA `fs10`
  - `f27 :: RISCV{32,64}Reg`, AKA `fs11`
  - `f28 :: RISCV{32,64}Reg`, AKA `ft8`
  - `f29 :: RISCV{32,64}Reg`, AKA `ft9`
  - `f30 :: RISCV{32,64}Reg`, AKA `ft10`
  - `f31 :: RISCV{32,64}Reg`, AKA `ft11`
  - `mvendorid :: RISCV{32,64}Reg`
  - `marchid :: RISCV{32,64}Reg`
  - `mimpid :: RISCV{32,64}Reg`
  - `mhartid :: RISCV{32,64}Reg`
  - `mstatus :: RISCV{32,64}Reg`
  - `misa :: RISCV{32,64}Reg`
  - `medeleg :: RISCV{32,64}Reg`
  - `mideleg :: RISCV{32,64}Reg`
  - `mie :: RISCV{32,64}Reg`
  - `mtvec :: RISCV{32,64}Reg`
  - `mcounteren :: RISCV{32,64}Reg`
  - `mscratch :: RISCV{32,64}Reg`
  - `mepc :: RISCV{32,64}Reg`
  - `mcause :: RISCV{32,64}Reg`
  - `mtval :: RISCV{32,64}Reg`
  - `mip :: RISCV{32,64}Reg`
  - `mcycle :: RISCV{32,64}Reg`
  - `minstret :: RISCV{32,64}Reg`
  - `mcycleh :: RISCV{32,64}Reg`
  - `minstreth :: RISCV{32,64}Reg`
  - `frm :: RISCV{32,64}Reg`
  - `fflags :: RISCV{32,64}Reg`
  - `fcsr :: RISCV{32,64}Reg`
  - `priv :: RISCV{32,64}Reg`
  - `exc :: RISCV{32,64}Reg`

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
