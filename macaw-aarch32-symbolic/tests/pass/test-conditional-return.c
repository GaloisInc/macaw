#include "util.h"

int g = -11;

int __attribute__((noinline)) test_conditional_return(int x, int y, int z) {
  // Note that this early return is entirely in terms of `x` because we are
  // trying to convince the compiler to generate a conditional return. If there
  // is too much here (e.g., register moves), it generally won't do it. Since
  // `x` is in r0 (and the return value is in r0), this usually convinces the
  // compiler to generate the necessary code.
  if(x > 0) return x;

  g = g + 1;
  g = g - y + x;
  int ret = y;
  if(ret <= 0) ret = 1;

  return ret;
}

void _start() {
  test_conditional_return(1, g, 0);
  EXIT();
}
