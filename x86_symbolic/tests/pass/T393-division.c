// A regression test for #393 which ensures that macaw-x86-symbolic's semantics
// for the `idiv` (signed division) and `div` (unsigned division) instructions
// compute the correct results.
//
// GCC is quite clever at optimizing away division-related instructions when one
// of the operands is a constant, so we have to define things somewhat
// indirectly to ensure that the resulting x86-64 assembly actually does contain
// `idiv` and `div`.

int __attribute__((noinline)) mod_signed(int x, int y) {
  return x % y;
}

int __attribute__((noinline)) test_mod_signed(void) {
  return mod_signed(1, 2);
}

int __attribute__((noinline)) div_signed(int x, int y) {
  return x / y;
}

int __attribute__((noinline)) test_div_signed(void) {
  return !div_signed(1, 2);
}

unsigned int __attribute__((noinline)) mod_unsigned(unsigned int x, unsigned int y) {
  return x % y;
}

unsigned int __attribute__((noinline)) test_mod_unsigned(void) {
  return mod_unsigned(1, 2);
}

unsigned int __attribute__((noinline)) div_unsigned(unsigned int x, unsigned int y) {
  return x / y;
}

unsigned int __attribute__((noinline)) test_div_unsigned(void) {
  return !div_unsigned(1, 2);
}

void _start(void) {
  test_mod_signed();
  test_div_signed();
  test_mod_unsigned();
  test_div_unsigned();
};
