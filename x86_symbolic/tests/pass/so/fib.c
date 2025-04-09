#include "fib.h"
#include "getone.h"

int fib(int n) {
  if (n <= 0) return 0;
  if (n == 1) return getone();
  return fib(n - 1) + fib(n - 2);
}
