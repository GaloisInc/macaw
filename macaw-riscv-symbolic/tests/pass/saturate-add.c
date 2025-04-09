#include <limits.h>

unsigned int __attribute__((noinline)) test_saturate_add(unsigned int x, unsigned int y) {
  unsigned int c = x + y;
  if(c < x || c < y)
    c = UINT_MAX;

  return c >= x && c >= y;
}

void _start() {
  test_saturate_add(1, 2);
}
