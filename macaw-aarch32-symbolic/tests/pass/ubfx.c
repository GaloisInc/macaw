
int __attribute__((noinline)) test_ubfx(unsigned int x) {
  unsigned int low_bits = x & 0x00000ff0;
  unsigned int y = 0;
  asm volatile (
          "ubfx    %[result], %[value], #4, #8\n\t"
          : [result] "=r" (y)
          : [value]"r" (x)
  );
  if (x == 0xcdabefab) {
      return (y == 0x000000fa) && (low_bits == 0x00000fa0);
  }
  return y == (low_bits >> 4);
}

void _start() {
  test_ubfx(1);
}
