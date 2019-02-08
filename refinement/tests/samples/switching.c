#include <stdint.h>

int64_t __ucmpdi2() {};
int64_t select(int64_t a, int64_t b)
{
    switch (a) {
    case 0: return b;
    case 1: return b+1;
    case 2: return b<<1;
    case 3: return b+b;
    case 4: return b<<2;
    case 5: return b+5;
    default: return 0;
    }
    // Has a "jmp rax", which is a classify failure "stmtsTerm = unknown transfer"
}

void _start()
{
  int64_t r = select(3, 4);
  return;
}
