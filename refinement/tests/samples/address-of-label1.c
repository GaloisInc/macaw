#include <stdint.h>

int64_t select(int64_t a, int64_t b)
{
  int64_t res = 5;
  void* targets[] = {&&case1, &&case2, &&case3};

  int idx = 0;
  if(a > 10)
    idx = 1;
  if(a < -5)
    idx = 2;
  goto *targets[idx];

  case1:
  res = res + b;
  case2:
  res = res - b;
  case3:
  res = res * b;


  return res;
}

void _start()
{
  int64_t r = select(3, 4);
  return;
}
