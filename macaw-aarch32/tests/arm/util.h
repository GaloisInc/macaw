#define EXIT() \
  asm("mov     %r7, $1");  \
  asm("svc #0")
