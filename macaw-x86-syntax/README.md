# macaw-x86-syntax

This package provides concrete syntax for macaw-x86-symbolic types and
operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types and operations:

**Types**:

- `X86Regs`: the struct of all x86_64 registers

**Operations**:

- `get-reg :: X86Reg -> X86Regs -> t`: extract an x86 register
- Registers:
  - `rip :: X86Reg`: instruction pointer

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
