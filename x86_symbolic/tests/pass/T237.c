#include <stdint.h>

// A test case which ensures that the `push` instruction decrements the stack
// pointer by 8 bytes in 64-bit mode, even if the source operand is an
// immediate that is less than 8 bytes.

int __attribute__((noinline)) test_push() {
  uint64_t ret = 0;
  __asm__(
    // 1. Save the address of the stack pointer to %13.
    "leaq 0x0(%%rsp), %%r13;"
    // 2. Push an immediate (which should be sign-extended to 8 bytes) on the
    //    stack.
    "pushq $0x0;"
    // 3. Save the difference between the old and new stack pointer addresses
    //    to %r13.
    "leaq 0x0(%%rsp), %%r14;"
    "subq %%r14, %%r13;"
    // 4. Pop the previously pushed immediate. (We no longer need %r14, so it
    //    is fine to write a temporary value here.)
    "popq %%r14;"
    // 5. Check if the stack pointer address difference is 8 bytes.
    //    If so, return 1. Otherwise, return 0.
    "cmpq $0x8, %%r13;"
    "sete %%al;"
    "movzbq %%al, %0;"
    : "=r"(ret) /* Outputs */
    : /* Inputs */
    : "%r13", "%r14" /* Clobbered registers */
    );
  return ret;
}

void _start() {
  test_push();
}
