# macaw-x86-syntax

This package provides concrete syntax for macaw-x86-symbolic types and
operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types and operations:

**Types**:

- `X86Regs`: the struct of all x86_64 registers

**Operations**:

- `get-reg :: X86Reg -> X86Regs -> t`: extract an x86 register
- `set-reg :: X86Reg -> t -> X86Regs -> X86Regs`: set an x86 register
- Registers:
  - `rip :: X86Reg`: instruction pointer
  - `rax :: X86Reg`: SysV return value register
  - `rbx :: X86Reg`: general-purpose register
  - `rcx :: X86Reg`: general-purpose register
  - `rdx :: X86Reg`: general-purpose register
  - `rsp :: X86Reg`: stack pointer
  - `rbp :: X86Reg`: base pointer
  - `rsi :: X86Reg`: general-purpose register
  - `rdi :: X86Reg`: general-purpose register
  - `r8 :: X86Reg`: general-purpose register
  - `r9 :: X86Reg`: general-purpose register
  - `r10 :: X86Reg`: general-purpose register
  - `r11 :: X86Reg`: general-purpose register
  - `r12 :: X86Reg`: general-purpose register
  - `r13 :: X86Reg`: general-purpose register
  - `r14 :: X86Reg`: general-purpose register
  - `r15 :: X86Reg`: general-purpose register
  - `cf :: X86Reg`: carry flag
  - `pf :: X86Reg`: parity flag
  - `af :: X86Reg`: auxiliary carry flag
  - `zf :: X86Reg`: zero flag
  - `sf :: X86Reg`: sign flag
  - `tf :: X86Reg`: trap flag
  - `ifl :: X86Reg`: interrupt enable flag
  - `df :: X86Reg`: direction flag
  - `of :: X86Reg`: overflow flag
  - `ie :: X86Reg`: x87 invalid operation exception flag
  - `de :: X86Reg`: x87 denormalized operand exception flag
  - `ze :: X86Reg`: x87 zero divide exception flag
  - `oe :: X86Reg`: x87 overflow exception flag
  - `ue :: X86Reg`: x87 underflow exception flag
  - `pe :: X86Reg`: x87 precision exception flag
  - `ef :: X86Reg`: x87 error summary flag
  - `es :: X86Reg`: x87 stack fault flag
  - `c0 :: X86Reg`: x87 condition code 0
  - `c1 :: X86Reg`: x87 condition code 1
  - `c2 :: X86Reg`: x87 condition code 2
  - `c3 :: X86Reg`: x87 condition code 3
  - `top :: X86Reg`: x87 top-of-stack pointer
  - `tag0 :: X86Reg`: x87 tag register 0
  - `tag1 :: X86Reg`: x87 tag register 1
  - `tag2 :: X86Reg`: x87 tag register 2
  - `tag3 :: X86Reg`: x87 tag register 3
  - `tag4 :: X86Reg`: x87 tag register 4
  - `tag5 :: X86Reg`: x87 tag register 5
  - `tag6 :: X86Reg`: x87 tag register 6
  - `tag7 :: X86Reg`: x87 tag register 7
  - `st0 :: X86Reg`: x87 FPU register 0 (alias: mm0)
  - `st1 :: X86Reg`: x87 FPU register 1 (alias: mm1)
  - `st2 :: X86Reg`: x87 FPU register 2 (alias: mm2)
  - `st3 :: X86Reg`: x87 FPU register 3 (alias: mm3)
  - `st4 :: X86Reg`: x87 FPU register 4 (alias: mm4)
  - `st5 :: X86Reg`: x87 FPU register 5 (alias: mm5)
  - `st6 :: X86Reg`: x87 FPU register 6 (alias: mm6)
  - `st7 :: X86Reg`: x87 FPU register 7 (alias: mm7)
  - `mm0 :: X86Reg`: MMX register 0 (alias: st0)
  - `mm1 :: X86Reg`: MMX register 1 (alias: st1)
  - `mm2 :: X86Reg`: MMX register 2 (alias: st2)
  - `mm3 :: X86Reg`: MMX register 3 (alias: st3)
  - `mm4 :: X86Reg`: MMX register 4 (alias: st4)
  - `mm5 :: X86Reg`: MMX register 5 (alias: st5)
  - `mm6 :: X86Reg`: MMX register 6 (alias: st6)
  - `mm7 :: X86Reg`: MMX register 7 (alias: st7)
  - `zmm0 :: X86Reg`: 512-bit vector register 0
  - `zmm1 :: X86Reg`: 512-bit vector register 1
  - `zmm2 :: X86Reg`: 512-bit vector register 2
  - `zmm3 :: X86Reg`: 512-bit vector register 3
  - `zmm4 :: X86Reg`: 512-bit vector register 4
  - `zmm5 :: X86Reg`: 512-bit vector register 5
  - `zmm6 :: X86Reg`: 512-bit vector register 6
  - `zmm7 :: X86Reg`: 512-bit vector register 7
  - `zmm8 :: X86Reg`: 512-bit vector register 8
  - `zmm9 :: X86Reg`: 512-bit vector register 9
  - `zmm10 :: X86Reg`: 512-bit vector register 10
  - `zmm11 :: X86Reg`: 512-bit vector register 11
  - `zmm12 :: X86Reg`: 512-bit vector register 12
  - `zmm13 :: X86Reg`: 512-bit vector register 13
  - `zmm14 :: X86Reg`: 512-bit vector register 14
  - `zmm15 :: X86Reg`: 512-bit vector register 15

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
