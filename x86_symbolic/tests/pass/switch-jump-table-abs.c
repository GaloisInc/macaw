// Regression test for #628.
//
// This switch on an unsigned char argument is lowered by the compiler to a
// jump table at -O2, gated by 32-bit comparisons on the argument register.
// From those comparisons, macaw's jump-bounds analysis infers a range on the
// argument. The bug being guarded against is recording that (32-bit-derived)
// range as a bound on all 64 bits of the register: a value whose low bits
// satisfy the guards but whose high bits are set still reaches the jump table,
// so a 64-bit bound would be unsound.
//
// The test harness installs the checked variant of MacawNarrowBVDomain (see
// Data.Macaw.Symbolic.Testing.withCheckedNarrowBVDomain), which adds an SMT
// proof obligation that the symbolic value actually lies within the abstract
// domain before narrowing. If the domain is unsound, that obligation is
// disproved and the test fails.

int __attribute__((noinline)) test_needs_escape(unsigned char c) {
    switch (c) {
    case 0x00 ... 0x1f:
    case 0x7f ... 0xff:
    case '\\': case '%': case '#': case '/':
    case '(': case ')': case '<': case '>':
    case '[': case ']': case '{': case '}':
        return 1;
    default:
        return 2;
    }
}

void _start() {
    test_needs_escape(0);
}
