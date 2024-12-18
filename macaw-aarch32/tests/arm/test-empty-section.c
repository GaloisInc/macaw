// test-empty-section.c
// test for issue #302 (https://github.com/GaloisInc/macaw/issues/302)
// results in a binary with an empty section when built as follows:
//
// arm-linux-gnueabi-gcc -nostartfiles -O2 -static test-empty-section.c -o test-empty-section-a32.exe
//
//
#include <stdint.h>

uint64_t x = 0;

int __attribute__((noinline)) test_strd() {
  x = 42;
  return x == 42;
}

int main() {
  test_strd();
  return 0;
}