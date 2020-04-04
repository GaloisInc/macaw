#include <stdint.h>

int64_t select(int64_t a, int64_t b)
{
  int64_t res = 5;
  void* targets[] = {&&case1, &&case2, &&case3};
  // This stack array (and its use later) are included to make sure that the
  // compiler uses some stack space for this function (even when optimizing).
  // Without stack use, macaw eagerly identifies the indirect jump as a tail
  // call, preventing the refinement code from firing.
  int stackArray[100];

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


  return res + stackArray[res];
}

void _start()
{
  int64_t r = select(3, 4);
  return;
}
