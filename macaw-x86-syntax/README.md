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

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
