# macaw-symbolic-syntax

This package provides concrete syntax for macaw-symbolic types and operations.

Concretely, it implements a `ParserHooks` for use with [`crucible-syntax`][syn].
This `ParserHooks` supports the following types and operations:

**Types**:

The main type addition is for representing pointers:

- `(Ptr n)`

Unlike C/C++, these pointers are untyped and essentially correspond to `uint8_t*`.

**Operations**:

The extra operations are:

- `bv-typed-literal :: Type -> Integer -> Bitvector w` where the first argument is a `Bitvector` type alias (see the Types section), the second argument is the value the `Bitvector` should contain, and `w` is the number of bits in the returned `Bitvector` (will match the width of the `Type` argument). This is useful because `(bv <width> ...)` only works when you know the exact value of width as a numeral, and types like `SizeT` map to different widths depending on your architecture.
- `pointer-make-null :: Pointer` returns a null pointer.
- `pointer-add :: Pointer -> Bitvector w -> Pointer` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-diff :: Pointer -> Pointer -> Bitvector w` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-sub :: Pointer -> Bitvector w -> Pointer` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-eq :: Pointer -> Pointer -> Bool`.
- `pointer-read :: forall (t :: Type) -> Endianness -> Pointer -> t` where the first argument is the type of the value to read and the second argument is `le` or `be`. `Type` must either be `Bitvector (8 * w)` (for some positive number `w`) or one of the type aliases listed above.
- `pointer-write :: forall (t :: Type) -> Endianness -> Pointer -> t -> Unit` where the first argument is the type of the value to read and the second argument is `le` or `be`. `Type` must either be `Bitvector (8 * w)` (for some positive number `w`) or one of the type aliases listed above.

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
