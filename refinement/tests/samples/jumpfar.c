#include <stdint.h>

int64_t rec_sum_bounce(int64_t v, int64_t running_total);

int64_t rec_sum(int64_t v, int64_t running_total)
{
    if (v == 0)
        return running_total;
    switch (v & 1) {
    case 0: return rec_sum_bounce(v - 1, running_total + v);
    case 1: return rec_sum(v, running_total);
    }
}

#ifdef __x86_64
#define SOME_CODE asm("\n\
    xor %rax, %rbx \n    \
    inc %rax \n          \
    sub $3, %rbx \n      \
        ");
#else
#ifdef __PPC__
#define SOME_CODE asm("\n\
        lis     %r2,4098 \n                    \
        addi    %r2,%r3,-32000 \n               \
        ld      %r2,-8(%r1) \n                  \
        rldicr  %r9, %r9, 1, 19 \n              \
        mflr    %r2 \n                         \
        ");
#else
#ifdef __arm__
#define SOME_CODE asm("\n\
    add %r0, %r1, %r2 \n          \
    sub %r4, %r0, #20 \n          \
    ldm %r2, {%r1, %r2} \n        \
    mov %r0, %r1\n                \
        ");
#else
#error unknown architecture
#endif
#endif
#endif

#define MORE_CODE SOME_CODE; SOME_CODE; SOME_CODE; SOME_CODE; SOME_CODE;
#define EXTRA_CODE MORE_CODE; MORE_CODE; MORE_CODE; MORE_CODE; MORE_CODE;
#define LOTS_CODE EXTRA_CODE; EXTRA_CODE; EXTRA_CODE; EXTRA_CODE; EXTRA_CODE;

int64_t some_code()
{
    LOTS_CODE;
    LOTS_CODE;
    LOTS_CODE;
    LOTS_CODE;
    LOTS_CODE;
    return 3;
}


int64_t rec_sum_bounce(int64_t v, int64_t running_total)
{
    int64_t (*next_step)(int64_t v, int64_t running_total) = (void*)0;

    if (v == 0)
        return running_total;
    switch (v & 1) {
    case 0: next_step = rec_sum;
    case 1: next_step = rec_sum_bounce;
    }
    (*next_step)(v - 1, running_total + v);
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
