#include <stdint.h>

// Similar to switching.c, but switching.c has only a single instance
// in a single function and this has multiple instances in multiple
// functions.

int64_t __ucmpdi2() {};
int64_t reflect(int64_t a, int64_t b, int64_t c)
{
    switch (b) {
    case 0: return b+5;
    case 1: return a+b;
    case 3: return a<<b;
    case 4: return a+3;
    case 5: return b+3;
    case 6: switch (a) {
        case 0: return b;
        case 1: return b+1;
        case 2: return b<<1;
        case 3: return b+b;
        case 4: return b+a;
        case 5: return b-a;
        case 6: switch (c) {
            case 0: return b<<2;
            case 1: return a<<2;
            case 2: return a>>2;
            case 3: return b>>2;
            case 4: return a^2;
            case 5: return b^2;
            default: return 1;
            }
        default: return ~0;
        }
    default: return 0;
    }
}

int64_t select(int64_t a, int64_t b)
{
    switch (a) {
    case 0: return b;
    case 1: return b+1;
    case 2: return b<<1;
    case 3: return b+b;
    case 4: return b<<2;
    case 5: switch (b) {
        case 0 : return b+5;
        case 1 : return a+b;
            // specifically missing case 2, should still generate a
            // jump expression.
        case 3 : return a<<b;
        case 4 : return b<<a;
        case 5 : return b<<1 + 1;
        default: return ~0;
        }
    default: return 0;
    }
    // Has a "jmp rax", which is a classify failure "stmtsTerm = unknown transfer"
}

void _start()
{
    int64_t r = reflect(select(3, 4), 1, 2);
    return;
}
