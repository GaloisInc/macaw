/*

This is a small file designed to create a minimal test of the symbolic simulator.

It can be compiled with:

  clang -o test_add.o -O2 -c -momit-leaf-frame-pointer test_add.c
*/

#include <stdint.h>

uint64_t add(uint64_t x, uint64_t y) {
    return x + y;
}
