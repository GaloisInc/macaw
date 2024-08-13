/**
 * A regression test for #420 which ensures that macaw-x86's semantics for the
 * `call` instruction are correct when the call target involves the stack
 * pointer. If we get it wrong, then the `call *0x8(%rsp)` instruction below
 * will call a nonsensical address.
 *
 * It is surprisingly difficult to get `gcc` to generate code with a
 * `call *0x8(%rsp)` instruction, so we resort to inline assembly to guarantee
 * that this happens.
 */

int one(void) {
  return 1;
}

int __attribute__((noinline)) test_callit(void) {
  int (*fn)(void) = &one;
  int ret = 0;
  __asm__(
    // 1. Decrement the stack pointer in preparation for storing `fn` on the
    //    stack.
    "sub $0x10,%%rsp;"
    // 2. Store the `fn` function pointer (passed as an input) on the stack.
    "mov  %1,0x8(%%rsp);"
    // 3. Load `fn` from the stack and call it. This is the key part of the
    //    test, as we want to ensure that macaw-x86's semantics for `call` will
    //    retrieve `fn` *before* pushing the next instruction's address onto the
    //    stack.
    "call *0x8(%%rsp);"
    // 4. Save the return value of `fn` as output.
    "mov %%eax, %0;"
    // 5. Increment the stack pointer back to its original position.
    "add $0x10,%%rsp;"
    : "=r"(ret) /* Outputs */
    : "r"(fn) /* Inputs */
    );
  return ret;
}

void _start() {
  test_callit();
}
