#include "fib.h"

int __attribute__((noinline)) test_fib(void) {
  return fib(6) == 8;
}

void _start(void) {
  test_fib();
}
