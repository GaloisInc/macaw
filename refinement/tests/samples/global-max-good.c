#include <stdint.h>

// A global to compare against
int64_t g = 5;

// Max of three values
int64_t max3(int64_t a, int64_t b)
{
  int64_t mx = a;
  if(mx <= b)
    mx = b;

  if(mx <= g)
    mx = g;

  return mx;
}

void _start()
{
  int64_t r = max3(3, 4);
  return;
}
