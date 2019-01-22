/*
  This file contains some functionality tests to assess properties of the
  ucomiss instruction.
 */
#include<stdbool.h>
#include<stdint.h>
#include<stdio.h>
#include<stdlib.h>
#include<stdarg.h>

/* Perform a ucomis on the two inputs and return the flag register. */
uint64_t do_ucomiss(float x, float y);

uint64_t get_mxcsr();

void set_mxcsr(uint64_t mxcsr);

typedef union {
    float f;
    uint32_t i;
} float_union;

static
float mk_float(uint32_t sign, uint8_t exp, uint32_t fraction) {
    float_union s;
    s.i = sign << 31 | exp << 23 | fraction;
    return s.f;
}

// Return the exponent value of a float
static
uint8_t float_exp(float f) {
    float_union s;
    s.f = f;
    return (s.i >> 23) & 0xff;
}

// Return the mantissa value of a float
static
uint8_t float_mantissa(float f) {
    float_union s;
    s.f = f;
    return s.i & 0x7fffff;
}

static
float mk_snan(uint32_t sign, uint32_t fraction) {
    uint32_t mask = (1 << 22) - 1;
    return mk_float(sign, 0xff, fraction & mask);
}

static
float mk_qnan(uint32_t sign, uint32_t fraction) {
    uint32_t mask = (1 << 22) - 1;
    return mk_float(sign, 0xff, (1 << 22) | (fraction & mask));
}

// Return true if the floating point is a nan.
static
bool float_is_nan(float f) {
    return (float_exp(f) == 0xff)
	&& (float_mantissa(f) != 0);
}

uint32_t float_bits(float x) {
    float_union s;
    s.f = x;
    return s.i;
}

bool get_cf(uint64_t flags) {
    return (flags & 0x01) != 0;
}

bool get_pf(uint64_t flags) {
    return (flags & 0x04) != 0;
}

bool get_zf(uint64_t flags) {
    return (flags & 0x40) != 0;
}

void my_assert(bool b, const char* fmt, ...) {
    if (!b) {
	va_list args;
	va_start(args, fmt);
	vfprintf(stderr, fmt, args);
	va_end(args);
    }
}

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
