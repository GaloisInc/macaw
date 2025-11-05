// Regression test for https://github.com/GaloisInc/macaw/issues/543

__attribute__((target("thumb")))
int __attribute__((noinline)) test_pop() {

  // manually put 'x' at the end of memory so that the LLVM memory
  // model will throw an error if more than 2 words are read from it
  int *x = (int*)0xfffffff6;

  int ret1;
  int ret2;
  // we pick the registers manually to ensure they're ascending
  asm volatile (
          "mov r3,sp\n\t"
          "ldr sp,%[x]\n\t"
          "pop {r1,r2}\n\t"
          "mov %[ret1],r1\n\t"
          "mov %[ret2],r2\n\t"
          "mov sp,r3"
          : [ret1]"=r" (ret1), [ret2]"=r" (ret2)
          : [x]"m" (x)
          : "r1","r2","r3"
  );
  return x[0] == ret1 && x[1] == ret2;
}

__attribute__((target("arm")))
void _start() {
  test_pop();
}