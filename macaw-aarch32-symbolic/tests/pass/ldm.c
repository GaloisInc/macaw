int x[5];

int __attribute__((noinline)) test_ldm() {
  int ret1;
  int ret2;
  // we pick the registers manually to ensure they're ascending
  asm volatile (
          "ldm    %[x], {r1,r2}\n mov %[ret1],r1\n mov %[ret2],r2"
          : [ret1]"=r" (ret1), [ret2]"=r" (ret2)
          : [x]"r" (x)
          : "r1","r2"
  );
  return x[0] == ret1 && x[1] == ret2;
}

void _start() {
  test_ldm();
}