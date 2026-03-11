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
- `bits-to-pointer :: Bitvector w -> Pointer` where `w` is the number of bits in a pointer (usually 32 or 64). This returns a pointer with a block number of 0 and an offset equal to the bitvector argument.
- `pointer-to-bits :: Pointer -> Bitvector w` where `w` is the number of bits in a pointer (usually 32 or 64). This returns a bitvector equal to the offset of the pointer argument. By default, this requires that the pointer argument have a block number of 0, and supplying a pointer with a non-zero block number will result in an assertion failure.
- `global-ptr :: Natural -> Natural -> Pointer` constructs a pointer from a region index and offset. Converts a memory address to an LLVM pointer.
- `pointer-add :: Pointer -> Bitvector w -> Pointer` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-diff :: Pointer -> Pointer -> Bitvector w` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-sub :: Pointer -> Bitvector w -> Pointer` where `w` is the number of bits in a pointer (usually 32 or 64).
- `pointer-and :: Pointer -> Pointer -> Pointer`
- `pointer-xor :: Pointer -> Pointer -> Pointer`
- `pointer-eq :: Pointer -> Pointer -> Bool`
- `pointer-leq :: Pointer -> Pointer -> Bool`
- `pointer-lt :: Pointer -> Pointer -> Bool`
- `pointer-mux :: Bool -> Pointer -> Pointer -> Pointer`
- `pointer-trunc :: Bitvector w -> Bitvector r -> Pointer w -> Pointer r` truncates a pointer from width `w` to smaller width `r`, where `(r + 1) <= w`.
- `pointer-uext :: Bitvector w -> Bitvector r -> Pointer w -> Pointer r` unsigned extends a pointer from width `w` to larger width `r`, where `(w + 1) <= r`.
- `pointer-read :: forall (t :: Type) -> Endianness -> Pointer -> t` where the first argument is the type of the value to read and the second argument is `le` or `be`. `Type` must either be `Bitvector (8 * w)` (for some positive number `w`) or one of the type aliases listed above.
- `pointer-write :: forall (t :: Type) -> Endianness -> Pointer -> t -> Unit` where the first argument is the type of the value to write and the second argument is `le` or `be`. `Type` must either be `Bitvector (8 * w)` (for some positive number `w`) or one of the type aliases listed above.
- `pointer-cond-read :: forall (t :: Type) -> Endianness -> Bool -> Pointer -> t -> t` conditionally reads memory based on a boolean condition. If the condition is true, reads from the pointer; otherwise returns the default value.
- `pointer-cond-write :: forall (t :: Type) -> Endianness -> Bool -> Pointer -> t -> Unit` conditionally writes memory based on a boolean condition. Only writes if the condition is true.
- `overflows :: OverflowOp -> Bitvector w -> Bitvector w -> Bitvector w -> Bool -> Bool` tests whether an arithmetic operation overflows. `OverflowOp` can be one of: `uadc` (unsigned add with carry), `sadc` (signed add with carry), `usbb` (unsigned subtract with borrow), or `ssbb` (signed subtract with borrow).
- `fresh-symbolic :: MacawType -> t` generates a fresh symbolic variable of the given Macaw type. `MacawType` can be `MacawBool` or `(MacawBV n)` for an `n`-bit bitvector.

[syn]: https://github.com/GaloisInc/crucible/tree/master/crucible-syntax
