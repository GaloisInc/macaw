#include <limits.h>

int __attribute__((noinline)) test_saturate_add(int x, int y) {
  int c = x + y;
  if(c < x || c < y)
    c = INT_MAX;

  return c >= x && c >= y;
}

void _start() {
  test_saturate_add(1, 2);
}
