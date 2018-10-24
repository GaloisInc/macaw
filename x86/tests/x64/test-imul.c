#include "util.h"

int g = -11;

void _start() {
  asm("mov %edx,0xc(%rsp)\n"
      "lea (%r12,%rax,1),%ecx\n"
      "xor %eax,%eax\n"
      "imul $0xffffffe8,%ebx,%ebx\n"
      "add %edi,%ebx\n"
      "mov %edx,%edi\n"
    );

  EXIT();
}
