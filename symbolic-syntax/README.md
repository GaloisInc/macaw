# macaw-symbolic-syntax

This package provides concrete syntax for macaw-symbolic types and operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types and operations:

**Types**:

The main type addition is for representing pointers:

- `Pointer`

Unlike C/C++, these pointers are untyped and essentially correspond to `uint8_t*`.

There are a few wrappers around `Bitvector` types for portability and convenience:

- `Byte` is an alias for `Bitvector 8`.
- `Int` is an alias for `Bitvector 32`.
- `Long` is an alias for `Bitvector 32` on Arm32 and `Bitvector 64` on X86_64.
- `PidT` is an alias for `Bitvector 32`.
- `Short` is an alias for `Bitvector 16`.
- `SizeT` is an alias for `Bitvector 32` on Arm32 and `Bitvector 64` on X86_64.
- `UidT` is an alias for `Bitvector 32`.

**Operations**:

The extra operations are:

- `bv-typed-literal :: Type -> Integer -> Bitvector w` where the first argument is a `Bitvector` type alias (see the Types section), the second argument is the value the `Bitvector` should contain, and `w` is the number of bits in the returned `Bitvector` (will match the width of the `Type` argument).
- `fresh-vec :: String Unicode -> forall (t :: Type) -> Nat -> Vector t`, where `(fresh-vec s t n)` generates a length-`n` vector where each element is a fresh constant of type `t` with the name `<s>_<i>` (for each `i` between `0` and `<n> - 1`). Note that `t` must be a scalar type (e.g., no nested `Vector`\ s), and `s` and `n` must both be concrete values.
- `pointer-make-null :: Pointer` returns a null pointer.
- `pointer-add :: Pointer -> Bitvector w -> Pointer` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-diff :: Pointer -> Pointer -> Bitvector w` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-sub :: Pointer -> Bitvector w -> Pointer` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-eq :: Pointer -> Pointer -> Bool`.
- `pointer-read :: forall (t :: Type) -> Endianness -> Pointer -> t` where the first argument is the type of the value to read and the second argument is `le` or `be`. `Type` must either be `Bitvector (8 * w)` (for some positive number `w`) or one of the type aliases listed above.
- `pointer-write :: forall (t :: Type) -> Endianness -> Pointer -> t -> Unit` where the first argument is the type of the value to read and the second argument is `le` or `be`. `Type` must either be `Bitvector (8 * w)` (for some positive number `w`) or one of the type aliases listed above.

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
