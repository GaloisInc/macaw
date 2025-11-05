// Regression test for https://github.com/GaloisInc/macaw/issues/266

int __attribute__((noinline)) test_ldm() {
  // manually put 'x' at the end of memory so that the LLVM memory
  // model will throw an error if more than 2 words are read from it
  int *x = (int*)0xfffffff6;
  int ret1;
  int ret2;
  // we pick the registers manually to ensure they're ascending
  asm volatile (
          "ldm    %[x], {r1,r2}\n mov %[ret1],r1\n mov %[ret2],r2"
          : [ret1]"=r" (ret1), [ret2]"=r" (ret2)
          : [x]"r" (x)
          : "r1","r2"
  );
  return (x[0] == ret1 && x[1] == ret2);
}

void _start() {
  test_ldm();
}