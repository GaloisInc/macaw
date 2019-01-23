#include <stdint.h>

int64_t rec_sum_bounce(int64_t v, int64_t running_total);

int64_t rec_sum(int64_t v, int64_t running_total)
{
    int i;

    if (v == 0)
        return running_total;
    for (i = 0; i < (v < 6 ? v : 6); i = ++i + 1) {
        running_total += 2;
    }
    return rec_sum(v - i, running_total + i);
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
