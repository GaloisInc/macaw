#include <stdint.h>

// A test case to test the simulator's EvenParity semantics
//
// After some changes to generalize LLVMPointer handling, we tickled some bad
// behavior around this primitive (see #260).

int __attribute__((noinline)) test_and_verify_parity(uint64_t x) {
  uint64_t stack_var;
  void* stack_addr = &stack_var;
  uint64_t ret = 1;
  __asm__(
    // Load an address into %rax; we need this to be a proper LLVMPointer (in
    // this case, a pointer into the stack, which is the only LLVMPointer we
    // have)
    "movq %1, %%rax;"
    // Add in a symbolic value so that constant propagation cannot possibly eliminate
    // the parity check
    "addq %2, %%rax;"
    // Use `test` to set the flags (including PF)
    "test %%rax, %%rax;"
    // Actually use PF so it doesn't get eliminated
    "jp end;"
    "movq $0, %0;"
    "end:"
    : "=r"(ret) /* Outputs */
    : "r"(stack_addr), "r"(x) /* Inputs */
    : "rax"
    );

  // We are returning either 1 or 0, so this test cannot be proven to return
  // 1. That is fine - we just want to make sure that the verifier evaluates
  // EvenParity without generating a failing goal.
  return ret;
}

void _start() {
  test_and_verify_parity(11);
}
