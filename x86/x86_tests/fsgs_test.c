// This file tests the push and mov instructions with segment registers.
#include "utils.h"
#include "expect_segfault.h"

uint64_t pushw_fs(uint16_t* p);
uint64_t pushq_fs(uint64_t* p);
uint64_t getw_fs();
uint64_t getq_fs();

void setw_fs(uint64_t x);
void setq_fs(uint64_t x);

// Setw that is expected to segfault.
void setw_illegal(void* arg) {
    setw_fs(5);
}

// Setq that is expected to segfault.
void setq_illegal(void* arg) {
    setq_fs(5);
}

int main(int argc, char** argv) {
    uint16_t w;
    uint64_t q;
    uint64_t sz;

    sz = pushw_fs(&w);
    my_assert(sz == 2, "pushw_fs size 2\n");
    my_assert(w  == 0, "pushw_fs result 0\n");

    sz = pushq_fs(&q);
    my_assert(sz == 8, "pushq_fs size 8\n");
    my_assert(q  == 0, "pushq_fs result 0\n");

    // Check getw and getq
    my_assert(getw_fs() == 0x123456789ab0000, "getw_fs is expected.");
    my_assert(getq_fs() == 0, "getq_fs is expected.");

    for (uint64_t i=0; i != 4; ++i) {
        setw_fs(0x10000 + i);
        my_assert(getq_fs() == i, "setwget expected");
    }
    expect_segfault(&setw_illegal, 0, "setw_illegal expected segfault.\n");
    expect_segfault(&setq_illegal, 0, "setq_illegal expected segfault.\n");
}
