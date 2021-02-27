// This test fails because x is not always 1
int __attribute__((noinline)) test_constant(int x) {
  return x == 1;
}

// Notes:
//
// - The entry point is required by the compiler to make an executable
//
// - We can't put the test directly in _start because macaw-symbolic (and macaw
//   in general) don't deal well with system calls
//
// - The test harness only looks for function symbols starting with test_
void _start() {
  test_constant(0);
}
