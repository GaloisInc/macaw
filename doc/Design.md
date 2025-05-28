This document describes the high-level design of macaw with pointers to more detailed design and implementation information.

# Overview

The macaw library provides binary code discovery (`macaw-base`) and symbolic execution (`macaw-symbolic`) for multiple Instruction Set Architectures (ISAs). See the [README](../README.md) for details on the currently-supported architectures. Each of the core pieces of functionality are implemented as a core architecture-independent library with architecture-specific libraries providing specializations (e.g., `macaw-base` and `macaw-x86`).

# Code Discovery

The binary code discovery problem is to identify all of the functions in a binary given at least one entry point (e.g., `main`). The code discovery algorithm is implemented in the `macaw-base` library. The design goals of macaw's code discovery implementation are:

- The results of code discovery should be *human readable* (i.e., simple enough to correspond to ISA manuals by eyeball)
- The implementation should be robust to failures and never throw exceptions/errors; instead, discovery failures should be explicitly represented in the IR and the algorithm should continue
- IR terms should be traceable to instructions
- No symbols or debug information should be required (but they should help if available)
- Control flow features should be identified semantically, rather than based on pattern matching instructions

## Intermediate Representation

The intermediate representation (IR) used by macaw is a simple [three address code](https://en.wikipedia.org/wiki/Three-address_code) style language similar to LLVM IR. The code discovery process produces a set of basic blocks, where each block ends in a terminator instruction. Each basic block has an address corresponding to the address of its first instruction. Control flow instructions target machine addresses (i.e., the CFG of the function is implicit and not reified in the structure of the IR).

The IR has unlimited virtual registers with each intermediate value being assigned to a distinct virtual register. Note that unlike LLVM IR, macaw IR is not in SSA form. The operations in the IR are primarily bitvector operations, which are polymorphic over bitvector width but strongly typed to ensure that bitvectors of different widths are not mixed without proper extension or truncation.

Note that the macaw IR does *not* have floating point operations; those are typically represented as architecture-specific extension statements. The macaw IR contains only the primitives necessary for recovering control flow. As a consequence, tricky hand-written assembly that uses e.g., bit-precise IEEE operations to directly compute an instruction address cannot be resolved by macaw (e.g., `jmp sqrt(foo)`).

## Core Algorithm

The core code discovery algorithm used by macaw (forced execution or recursive disassembly) is sketched out in the figure below:

```
             +-----------+          +--------------------+        +-----------------+
             |Entry Point|          |Exploration Frontier|        |Disassemble Block|
             |Address(es)----------->                    --------->                 <---------
             +-----------+          |                    |        |                 |        |
                                    +-------^------------+        +---------|-------+        |
                                            |                               |                |
                                            |                               |                |
                                            |                     +---------v-------+        |
                                            |                     |Rewrite          |        | Branch
                                            |                     |(Simplify)       |        |
                                            |                     |                 |        |
                                            |                     +---------|-------+        |
                                            |                               |                |
                                       Call |                               |                |
                                            |                     +---------v-------+        |
                                            |                     |Classify         |        |
                                            |----------------------                 ---------|
                                                                  |                 |
                                                                  +---------|-------+
                                                                            |
                                                                            | Return
                                                                      +-----v----+
                                                                      |Discovered|
                                                                      |Functions |
                                                                      +----------+
```
[Edit Diagram](http://buttersquid.ink/scribble.html?spore=bNobwRALmBcYE4FMDGUA0YAeMDMA2dAnjAOzoDuMATAIzoAWMALOgGZIxgAEYrLMADOgA2AeyzQAtAA5hIotFqQhMcEKiwAohgAOouAEMIASxEA7TgDE4Z4wjg8wQgG4CAvq9Th1kAEZiH4tTYhCToEBjeGqYQcAScAAoiRtEAOqYAggAmmYgAzrkAFAi5AJQOLtAxAK4IHl4cQskIAdRUAKzoGJQ4+GAErdAAnITdQ+gI+gLjPjCKouKUsvKCSiqO3ilV-NutwhX87p6QHBB+WJ09IdCkkBEcWroiBsZmltbRRnblMCz6Qrm1I7eRAoAIwXC9eQ3CgKGRgBjQZhgNgcbi8KaOfySXqieSKCDKaCqDZbHYOZxuOrHWCnfwXaAQq43cLeAAiRly+nyCAAtj4hAhOAAhURIADW32gv3+gPqsBBaEw4MhsyRMOocIRSJRsDRyL40BW8xgEhxclmYUJxI4m22-F2jn2hzlvjpSoZKoUSJZHAASggyHAjBAEGkCgBlIw83RGFgEMroCrSgFU4HIRXiRl9KiKdWapisdi6hwsA1GrGmpYW1ZE9Y20n28lO1MnM5gj1XGhhO6wADCQi5uVjRETPz+KaBDSaLRgbRuXWVhAGwz6oxXEwxCBmClkCyrhstazU9btDophud1Mc086A2IvQX10hA2oigIo2oSI3B7AW+rxugRZMWWQ9a2PWBbTJPZKUnWBGlMZpbxIB9RnvJdZjhd8c3GSYfz-HdMT3YCMQJI8SVPJsYJdeDEMwAYs0fRgkX6KhglXVicM3bdyyI3ESKtOsIIbM9m1g68EJnREkUY5iBkoNisIURRvxWfC5ixIC+J-UiwPIqDHSoq9aXOd1sEw2YVx9Ps-mUUcpXHWUrxoySpGktcFLkhTRnkzi8O43ccH3FYdOtISKOgi8Wzgm86JgQY2MfeL0MAry4t81T-MIqggtA0KwEgxsIoOKLxNojBlwS0ZXOSldFPXXCMv-DScprPKCpEwzvGM9tBmY1Vu28IUDFMJAGDs5NHK6tt6WIFZ5EoOErLAdlciQEQnDsBBMjSCwqhGl5TFySVqkmqcJKQp9OlQ592hGKg4RU6Ymt481tIE8D8uEyjIrE7qZpuebeiW-0ICqOBTElCbXAAXSAA)

The algorithm disassembles one function at a time by taking candidate function addresses from the *exploration frontier*, which is seeded with an initial set of entry point addresses. Typically, those addresses are at least the program entry point or the dynamic entry points of a shared library. Entry points can also include the addresses of static symbols if they are available (i.e., the binary is not stripped).

### Decoding

The decoding process uses the `disassembleFn` from the `ArchitectureInfo`, which has a notional type `ByteString -> Maybe (Instruction, ByteString)`. In practice the type is somewhat more complicated---see the source for details.

Macaw discovers functions by decoding their blocks individually. The block decoding loop:

1. Decodes an instruction using the low-level disassembly function
2. Lifts the instruction into a semantic representation (i.e., a sequence of Macaw IR instructions that encode the semantics of the instruction)
3. Decides if the instruction is a control flow instruction by inspecting the next value of the instruction pointer; if it is a control flow instruction, the decoder terminates the block (otherwise it continues decoding at (1))

Each block produced at this stage is of type `Block arch ids`. A `Block` is a sequence of Macaw IR instructions that manipulate the machine state followed by a block terminator, which is one of:
- `FetchAndExecute`, which indicates that the value of the instruction pointer must be interpreted to determine the target of a control flow transfer
- `TranslateError`, which indicates that decoding has failed (e.g., due to a disassembly error or missing semantics)
- `ArchTermStmt`, which encodes architecture-specific control flow that cannot be otherwise represented in the core Macaw IR

Notes:
- The `ids` type parameter is unique to the function being decoded and is ultimately quantified away to ensure that values and instructions from different functions cannot be mixed without an explicit renaming step.
- The actual `disassembleFn` takes an additional parameter that indicates a maximum offset to read from; this is used to enable block splitting when macaw finds a jump into the middle of a known block.

### Rewriting

Next, Macaw rewrites the `Block` to simplify terms, with the goal of improving readability and simplifying later analysis. The set of rewrites is ad-hoc, and attempts to balance efficiency with readability. It is not ideal, but some of the analyses performed by Macaw depend on specific rewrites firing in ways that are not documented well.

### Analysis

In the next step of the algorithm, Macaw needs to compute the next possible values of the instruction pointer to determine what kind of control flow transfer instruction terminates the `Block`. One key challenge in this is that individual blocks often do not have sufficient context to determine the next instruction pointer value; this especially arises in the presence of indirect (computed) jumps. To address this challenge, Macaw uses two phases of analysis: local (within a single block) and intraprocedural (between blocks in a function).

At the level of a single `Block`, Macaw starts its analysis with abstract symbolic "initial" values in every machine register. Within a block, it applies any simplifications it can in the presence of these abstract initial values. It complements this local analysis with abstract interpretation between blocks. The function entry point starts with an abstract initial state, with a few exceptions:
- Macaw manages the instruction pointer specially, and populates it according to the results of code discovery
- Macaw manages the return address specially, treating it as a distinct abstract value; each architecture backend is responsible for ensuring that the abstract return address is in the correct location
- Each architecture backend has a hook (`mkInitialAbsState`) to enable it to modify the initial abstract state (e.g., to handle dedicated registers in particular ABIs)

As each block is discovered, Macaw computes an updated abstract domain for it (starting with the final abstract state from all successors).

```
                                                      +-------------------+
                                  +-----+-----<-------|Initial Abstraction|
                                  |Entry|     |       +-------------------+
                                  +-----+     |          α
                                  |           |
                                  |           |       +----+
                                  +-----|-----<-------|abs1|
                                        |             +----+
                                        |
                                  +-----v-----+
                                  |           |         α
                                  |           |
                                  |           |
                                  |           |      +----+
                                  +-----------<-------abs2|
                                                     +----+
```
[Edit Diagram](http://buttersquid.ink/scribble.html#?spore=bNobwRALmBcYE4FMDGUA0YAeMDMAWdAnjugO4wCMATOgBYwCs6AZkjGAARjNMwAM6AGwD2WaAFpsgoUWj9IAmOAFRYAHQCuvLeS5gBANz4BfI6nArIAIxG7ReQsUgYLAUQB2EOEXSHon9Qim5mwQ1ljoovT4YDLUThYAkm4AlhDJAIYC7ACClgDOnukoyUJuur7+gWaQbALJbgi2OtBREZQwuABshM2SMe3QfQjpfOgIlhRSonHCMnIQCtBKFhpavDqCvrwm1RaIKLY40TLk5KQUcXQtzKywnNyjejbifbOPC4p6K5raugbGQRqsFCNgiDGOMDiEGcbCSqQyWVyBTgRTSpXKMEqgIsIPCmHBDmgAHZ0NCLOl8hswBU4AFsSEwocWhDiaSYbAKXkqTS6btavVGhFmq1MAMuj0YAAOQgDaVgYaPcaTJ7TKRzUmLZZsVa-TYAvnAxlglrdGIdNkWQCNwBjoExMnkqsFYHUGk0OnIMGK5ARmnKCANTmMRrIxhNoGcVZC1e9NV9tT91n8tjsnVZQfjmYSSfE2JzuZjaY6gWm8ZE+idGDmOfl2j4C7zU7imfRKycI2S2Na67b7UWLC7BZhhX1PR1TT6KOOA6aFSH5WGI8JVU91fJPsp42sqf9ZCYALpAA)

The abstract domains tracked by Macaw during this analysis include:
- Finite sets (with constant propagation)
- A relational stack domain (to identify abstract stack locations independent of the frame and stack pointers)
- A relational value domain, `IntraJumpBounds` (to track relations between values to reflect bounds checks and assist in jump table identification)
- Strided intervals

This is most of the Value Set Analysis (VSA), but is not exactly VSA. Together, these abstract domains enable tracking a few key values that are needed for control flow instruction classification:
- The abstract return address
- The addresses and bounds of jump tables

Notes:
- The abstract domains are currently somewhat unsound (e.g., writing a value to `TopV` doesn't necessarily clobber the entire stack)
- Transfer function coverage is incomplete (e.g., for various arithmetic operations) and has been improved as-needed
- Calls are optimistically assumed to preserve the same registers as required by the ABI; this is not correct in general, as static functions can violate this assumption

### Classification

In this step of the analysis, Macaw transforms a `Block` into a `ParsedBlock`, which is a refinement that has more specific control flow terminators that are identified by *classifying* the `FetchAndExecute` terminator into one of the more structured possibilities:
- Jump (to an address)
- Conditional Branch (on a condition to one of two successors)
- Call (either direct or indirect)
- Return
- Lookup Table Jump (local indirect jump through a jump table)
- Architecture-specific Terminator

The classification process uses the abstract values computed for each machine location via abstract interpretation. Several of the detectors are parameterized via `ArchInfo` functions including `identifyCall` and `identifyReturn`. The different classifiers are documented in the code. At a high level, they attempt to recognize their respective control flow constructs semantically (i.e., based on the Macaw semantics and not based on matching against individual instructions). Macaw applies the different classifiers in a pre-determined order by default; some of the aspects of the ordering are important and documented in the code. The classifier used for an architecture is actually a member of the `ArchInfo` (specifically `archClassifier`), enabling callers to customize it if they have special code discovery needs.

Targets of calls are added to the exploration frontier as they are identified. Each function is assigned a reason that Macaw has considered it as a function entry point to improve traceability.  Each discovered function is represented as a `DiscoveryFunInfo`, which contains the basic blocks of the function along with additional metadata.

Notes:
- The current design does not support unstructured (i.e., non-jump table) indirect local jumps
- There are currently unsafe assumptions about registers preserved across calls.
- The classifier strategy is exposed through the `ArchitectureInfo` and can be overridden as-needed

## Address Representations

There are several different representations of addresses in Macaw, which often leads to confusion. `MemAddr`, `MemWord`, and `MemSegmentOff` are used in conjunction with the *pre-loader* view of memory. They are disambiguated in the module-level documentation for `Data.Macaw.Memory`.

The notion of pointer used during symbolic execution is called `LLVMPointer`. These consist of a pair of a *block number* and an *offset*, see [the Crucible-LLVM docs].

[the Crucible-LLVM docs]: https://github.com/GaloisInc/crucible/blob/master/crucible-llvm/doc/memory-model.md

Note that Macaw currently assumes that addresses can either be 32 or 64 bits, and that the address size is uniform for a given architecture. In principle, supporting 16 or 128 bit addresses is possible, but doing so would require a careful audit.

## Architecture-specific Support

While the core discovery algorithms in macaw are architecture-independent, the core IR is not expressive enough to support all operations for all ISAs. Macaw parameterizes the core algorithms by architecture through the `ArchitectureInfo` type, which contains all architecture-specific heuristics/patterns. Macaw also allows architecture-specific extension expressions and statements to support the full range of instructions across architectures. Extensions can represent either additional primitive operations or entire instructions. Generally, floating point operations and meta-operations (e.g., cache control or concurrency) are represented as extensions. This structure is intended to keep the core language and analysis small to ensure readability; extensions are represented using idiomatic names, rather than being expressed as impenetrable blocks of IR statements.

Note that extensions can be expressions, statements, or terminator statements in the IR. Expressions are generally used for pure operations (e.g., approximate inverse square root). Statements have access to the entire machine state when they are evaluated (e.g., during symbolic execution).

While extensions are generally used to represent ISA features that are irrelevant to code discovery (e.g., floating point operations), that is not a requirement. The effects of extensions can be reflected into the core analysis by ensuring that they have faithful abstract transfer functions defined in the `ArchitectureInfo` type.

## Testing

Macaw's code discovery is mostly tested with integration tests by running the code discovery algorithm over small binaries and comparing the results to hand-written expected results. Most of the expected results encode expectations about the starting addresses and sizes of blocks.

Note that the tests are in the architecture-specific backends, as the code discovery loop must be instantiated with architecture details to be run at all. The core could be tested on a simplified testing architecture, but that would be a substantial amount of work for minimal additional payoff, as the code discovery is well-tested by the architecture-specific backends.

## Open Problems

There are a few major open challenges in the core Macaw code discovery implementation, which are documented in this section.

### Computed jumps

While Macaw supports detecting some jump tables, support is incomplete in the presence of a wide variety of compiler flags.  Optimizations can make recognizing some patterns difficult, while the variety of different jump table encodings is non-trivial to handle. For example, code generation with/without Position Independent Code (PIC) is substantially different. Related, jump tables can contain addresses *or* offsets, while in the case of offsets, the offsets can be relative to different program constructs.  Some of these cases are handled, but there is currently not a systematic accounting for which cases work, nor is there good regression tracking.

In the even more challenging case, Macaw has no support for computed jumps that are not based on jump tables. These arise in the presence of hand-written assembly and uses of the [address-of-label extension](https://gcc.gnu.org/onlinedocs/gcc/Labels-as-Values.html). To handle these, the core Macaw IR will need to be augmented with a new block terminator, along with supporting analysis infrastructure to determine possible jump targets.  The [macaw-refinement](../refinement/README.md) library provides one algorithmic approach to solve the problem.

### Revisiting functions with new information

A number of the classifiers in Macaw depend on previously-discovered information. Examples include the branch classifier, which will refuse to treat a jump as an intraprocedural branch if the target has been identified as a function entry point by some other means. However, if a control flow transfer was identified as an intraprocedural branch but where the target is *later* discovered to be a function entry point, Macaw will not re-visit affected functions to refine its results.

Enabling Macaw to compute a global fixed point will substantially improve code discovery results. Improved results will include at least:
- Improved recognition of tail calls
- More consistent splitting of basic blocks

### No-return Functions

When compiling C/C++, the compiler is aware of a small set of functions that do not return (usually via in-built heuristics or function attributes). The C/C++ compiler users this information to optimize calls that never return (i.e., by not including any location for the call to return to). This is great for execution, but problematic for code discovery.

As Macaw does not know which functions return and which do not, it always attempts to explore the instructions after a call; if the compiler has performed a no-return optimization, the following code will be junk and generate false positives.

Currently, Macaw has a facility (the `trustedFunctionEntryPoints` in the `DiscoveryState`) for marking functions as known to not return. This is sufficient to enable Macaw to ignore spurious code that cannot be executed. However, it does require manual specification. The situation could be improved by automating the analysis and identification of (transitive) no-return functions. This could be an additional heuristic in macaw-refinement.

### Function pointer identification

Much of the discussion of code discovery above hinges on the population and processing of the *exploration frontier*, which is the set of discovered function entry points. The caller must seed the analysis with at least one entry point, which enables the analysis to iteratively expand the frontier as more call targets are identified. This process works well for direct calls, but is a challenge in the presence of function pointers.

The initial design of macaw included (and still includes) a heuristic to treat any values that look like function pointers and are written to memory as if they were function pointers and add them to the exploration frontier. The heuristic determines that a value "looks like" a function pointer if it is a bitvector that, if interpreted as a pointer, would point into the `.text` (i.e., code) section of the binary. This heuristic was originally designed for non-PIC code, where code is typically at high addresses. However, this heuristic is problematic in PIC code where the `.text` section starts at a very low address (e.g., 0x100) and thus causes nearly every integer literal in the program to look like a potentially valid function address.

Longer term, Macaw will need a more principled approach to identify function pointers. This will likely be a combination of type inference and pointer analysis.

# Symbolic Execution

Besides binary code discovery, the other major service provided by the Macaw library (and specifically `macaw-symbolic`) is lifting machine code programs into Crucible IR to support symbolic execution.  After translation, callers can use the Crucible library to symbolically execute machine code.

## Translation

The Macaw IR is very close to the Crucible IR, so the translation step is fairly straightforward at the level of individual operations. Authors of architecture-specific backends must provide embeddings of Macaw architecture-specific expressions and statements into Crucible IR, as well as symbolic execution-time interpretations of those operations.

Recall that the Macaw IR does not directly represent control flow, instead representing each function as a collection of basic blocks. The translation into Crucible IR constructs an explicit CFG. In this translation, every function takes a single argument and returns a single value: a structure containing all of the machine registers. That structure is re-constituted between (most) basic blocks so that the arguments to each Crucible basic block are a full set of registers. However, within basic blocks, there is no easy way to access a specific machine register value post-translation; during translation, the mapping from abstract locals to machine registers is maintained. The major consequence of this is that overrides and syntax extension interpretations only have access to the machine register values that they are passed syntactically: they cannot access arbitrary machine state.

## Testing

The test suites for Macaw's symbolic backends is based on symbolic execution where each test function returns a value that the test harness attempts to prove is not zero. That is: each test case is essentially an assertion. Test cases in the architecture-specific test suites are crafted to encode verifiable (or falsifiable) assertions.

These test suites include harness code that can persist both the recovered Macaw CFGs and the Crucible CFGs for each function.

