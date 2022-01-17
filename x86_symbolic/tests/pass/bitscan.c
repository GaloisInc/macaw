#include <stdint.h>

int __attribute__((noinline)) test_bsf(uint64_t x) {
	uint64_t ret = 0;
	__asm__(
		"bsf %[x], %[ret]"
		: [ret] "=a"(ret)
		: [x] "b"(x)
		);
	uint64_t idx = 0;
	if (x == 0) return 1;
	while (!(x & 1)) {
		++idx;
		x >>= 1;
	}
	return idx == ret;
}

int __attribute__((noinline)) test_bsr(uint64_t x) {
	uint64_t ret = 0;
	__asm__(
		"bsr %[x], %[ret]"
		: [ret] "=a"(ret)
		: [x] "b"(x)
		);
	uint64_t idx = 0;
	while (x >>= 1) ++idx;
	return idx == ret;
}

void _start() {
	test_bsf(1);
	test_bsr(1);
};
