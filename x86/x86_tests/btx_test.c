/*
  This file contains some functionality tests to assess properties of the
  btc, btr, and bts instructions.
 */
#include<stdbool.h>
#include<stdint.h>
#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>

#include "utils.h"

uint64_t btc64_addr_reg(uint64_t* addr, uint64_t idx);
uint64_t btr64_addr_reg(uint64_t* addr, uint64_t idx);
uint64_t bts64_addr_reg(uint64_t* addr, uint64_t idx);
uint64_t bts64_addr_imm4(uint64_t* addr);
uint64_t bts64_addr_imm68(uint64_t* addr);


uint64_t btc_expected(uint64_t x, uint64_t v) {
    return x ^ v;
}

uint64_t btr_expected(uint64_t x, uint64_t v) {
    return x & ~v;
}

uint64_t bts_expected(uint64_t x, uint64_t v) {
    return x | v;
}

void test_addr_reg(const char* nm, uint64_t f(uint64_t*, uint64_t), uint64_t g(uint64_t, uint64_t)) {
    uint64_t a0 = 0x0123456789abcdef;
    for (uint64_t i = 0; i != 256; ++i) {

	uint64_t a[] = {a0, a0, a0, a0};
	uint64_t r = f(a, i);
	uint64_t val = (uint64_t) 1 << (i % 64);
	for (int j = 0; j != 4; ++j) {
	    uint64_t expected = (i / 64 == j) ? g(a0, val) : a0;
	    my_assert(a[j] == expected, "%s invalid %d %d %llx %llx\n", nm, i, j, a[j], expected);
	}
	bool expected_r = (a0 & val) != 0;
	my_assert(get_cf(r) == expected_r, "Bad %lld %llx %llx\n", i, expected_r, r);

    }
}

void test_addr_imm(const char* nm, uint64_t f(uint64_t*), uint64_t i, uint64_t g(uint64_t, uint64_t)) {
    uint64_t a0 = 0;

    uint64_t a[] = {a0, a0, a0, a0};
    uint64_t r  = f(a);

    uint64_t val = (uint64_t) 1 << (i % 64);
    for (int j = 0; j != 4; ++j) {
        uint64_t expected = (0 == j) ? g(a0, val) : a0;
	my_assert(a[j] == expected, "%s invalid %d %d %llx %llx\n", nm, i, j, a[j], expected);
    }
    uint64_t r_mask = 1;
    uint64_t expected_r = (a0 & val) ? 1 : 0;
    my_assert((r & r_mask) == expected_r, "Bad %lld %llx %llx\n", i, expected_r, r);
}

int main(int argc, char** argv) {
    test_addr_reg("btc64_addr_reg", &btc64_addr_reg, &btc_expected);
    test_addr_reg("btr64_addr_reg", &btr64_addr_reg, &btr_expected);
    test_addr_reg("bts64_addr_reg", &bts64_addr_reg, &bts_expected);

    test_addr_imm("bts64_addr_imm04", &bts64_addr_imm4, 4, &bts_expected);
    test_addr_imm("bts64_addr_imm68", &bts64_addr_imm68, 68, &bts_expected);

    return 0;
}
