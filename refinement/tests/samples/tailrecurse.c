#include <stdint.h>

int64_t rec_sum(int64_t v, int64_t running_total)
{
    if (v == 0)
        return running_total;
    return rec_sum(v - 1, running_total + v);
}

int64_t sum(int64_t a)
{
    return rec_sum(a, 0);
}

void _start()
{
  int64_t r = rec_sum(3, 4);
  return;
}
