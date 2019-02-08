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
    // Has a "jmp rax", which is a classify failure "stmtsTerm =
    // unknown transfer".  Note that it seems to require at least 6
    // case branch targets (for GCC 7.4.0 with -O0) to create a
    // computed branch target; fewer case targets just implement
    // explicit jumps.
}

void _start()
{
  int64_t r = select(3, 4);
  return;
}
