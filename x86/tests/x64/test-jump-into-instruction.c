#include "util.h"

void _start() {
  long long x;
here:
  // This makes an instruction with a short 0x90 nop slide.
  x = 0x9090909090909090;
  // The +4 is completely ignored by gcc. You have to modify the assembly by
  // hand after compiling to make this jump into the middle of an emitted
  // instruction.
  goto *(&&here + 4);
  EXIT();
}
