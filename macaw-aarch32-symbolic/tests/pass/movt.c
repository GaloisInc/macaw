// A test case which ensures that the `movt` instruction works as expected.
int __attribute__((noinline)) test_movt(void) {
  int ret = 0;
  // After the movt instruction, the value of r0 should be 0x10000, which
  // should suffice to make the `movne %0 #1` instruction fire and set the
  // value of ret (i.e., %0) to 1.
  __asm__(
  "movw      r6, #0x0;"
  "movt      r6, #0x1;"
  "cmp       r6, #0x0;"
  "movne     %0, #1;"
  : "=r"(ret) /* Outputs */
  : /* Inputs */
  : "r6", "r7" /* Clobbered registers */
  );
  return ret;
}

void _start() {
  test_movt();
}
