#include "util.h"

int gin = 1;
int g0 = 0;
int g1;
int g2;
int g3;
int g4;

int res;

long mod_5(long n, long i0, long i1, long i2, long i3, long i4){
beginning:
  switch(n)
  {
    case 0: res = res + i0; break;
    case 1: res = res + i1; break;
    case 2: res = res + i2; break;
    case 3: res = res + i3; break;
    case 4: res = res + i4; break;
    default: n = n - 5; goto beginning;
  }
}


void entry() {
  long in = (long)&gin;
  long i0 = (long)&g0;
  long i1 = (long)&g1;
  long i2 = (long)&g2;
  long i3 = (long)&g3;
  long i4 = (long)&g4;
  res = mod_5(gin, i0, i1, i2, i3, i4);
}

#if defined(NOSTDLIB)
void _start() {
  entry();
  EXIT(0);
}
#else
int main() {
  entry();
  return 0;
}
#endif
