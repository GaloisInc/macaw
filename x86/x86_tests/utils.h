// Functions needed by multiple test cases

// Assert condition is true, and exit if not.
static
void my_assert(bool b, const char* fmt, ...) {
    if (!b) {
	va_list args;
	va_start(args, fmt);
	vfprintf(stderr, fmt, args);
	va_end(args);
	exit(-1);
    }
}

////////////////////////////////////////////////////////////////////////
// Flags register access

static
bool get_cf(uint64_t flags) {
    return (flags & 0x01) != 0;
}

static
bool get_pf(uint64_t flags) {
    return (flags & 0x04) != 0;
}

static
bool get_zf(uint64_t flags) {
    return (flags & 0x40) != 0;
}


////////////////////////////////////////////////////////////////////////
// Floating point maniuplation.

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

// Return the bits in the float
uint32_t float_bits(float x) {
    float_union s;
    s.f = x;
    return s.i;
}
