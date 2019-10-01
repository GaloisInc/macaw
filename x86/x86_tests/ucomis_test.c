/*
  This file contains some functionality tests to assess properties of the
  ucomiss instruction.
 */
#include<stdbool.h>
#include<stdint.h>
#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>

#include "utils.h"

// Clear the flags register, oerform a ucomis on the two inputs, and
// return the flag register.
uint64_t do_ucomiss(float x, float y);

uint64_t get_mxcsr();

void set_mxcsr(uint64_t mxcsr);

int main(int argc, char** argv) {
    set_mxcsr(0x1f01);

    // test mk_float
    if (mk_float(0, 127, 0) != 1.0) {
	fprintf(stderr, "Unexpected float\n");
	return -1;
    }
    if (mk_float(0, 128, 0) != 2.0) {
	fprintf(stderr, "Unexpected float\n");
	return -1;
    }
    if (mk_float(1, 128, 0) != -2.0) {
	fprintf(stderr, "Unexpected float\n");
	return -1;
    }

    float qnan = mk_qnan(0, 1);
    if (float_bits(qnan) != 0x7fc00001) {
	fprintf(stderr, "Unexpected float\n");
	return -1;
    }
    if (!float_is_nan(qnan)) {
	fprintf(stderr, "Unexpected float\n");
	return -1;
    }

    // Test snan
    float snan = mk_snan(0, 1);
    if (float_bits(snan) != 0x7f800001) {
	fprintf(stderr, "Unexpected float\n");
	return -1;
    }
    if (!float_is_nan(snan)) {
	fprintf(stderr, "Unexpected float\n");
	return -1;
    }

    uint64_t r = do_ucomiss(0, 1);
    my_assert( get_cf(r), "Unexpected cf ucomiss(0,1)");
    my_assert(!get_pf(r), "Unexpected pf ucomiss(0,1)");
    my_assert(!get_zf(r), "Unexpected zf ucomiss(0,1)");

    r = do_ucomiss(1, 0);
    my_assert(!get_cf(r), "Unexpected cf ucomiss(1,0)");
    my_assert(!get_pf(r), "Unexpected pf ucomiss(1,0)");
    my_assert(!get_zf(r), "Unexpected zf ucomiss(1,0)");

    r = do_ucomiss(1, 1);
    my_assert(!get_cf(r), "Unexpected cf ucomiss(1,1)");
    my_assert(!get_pf(r), "Unexpected pf ucomiss(1,1)");
    my_assert( get_zf(r), "Unexpected zf ucomiss(1,1)");

    return 0;
}
