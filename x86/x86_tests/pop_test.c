/*
  This file contains some functionality tests to assess properties of ret.
 */
#include<stdbool.h>
#include<stdint.h>
#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>

#include "utils.h"

void pop_sp(uint64_t val, uint64_t* rsp0, uint64_t* rsp1);
void pop_rsp(uint64_t val, uint64_t* rsp0);

int main(int argc, char** argv) {
    uint64_t rsp0;
    uint64_t rsp1;
    pop_rsp(0xdeadbeefdeadbeef, &rsp1);
    my_assert(rsp1 == 0xdeadbeefdeadbeef, "Expected pop_rsp to return first value.\n");
    pop_sp(0xdead, &rsp0, &rsp1);
    // pop_sp should ensure the upper 48 bits have been incremented.
    my_assert((rsp0 >> 16) + 1 == (rsp1 >> 16), "Expected pop_rsp to return first value.\n");
    my_assert((rsp1 & 0xffff) == 0xdead, "Expected pop_rsp to return first value.\n");

    return 0;
}
