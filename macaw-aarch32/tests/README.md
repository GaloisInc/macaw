# Overview
The tests in this directory attempt to test both ARM and Thumb decoding/discovery.  The test suite only runs on the binaries with corresponding `.mcw.expected` files, which describe the expected discovered basic blocks.

- *test-just-exit-a32.exe*: Ensures that the very basics of anything at all works
- *test-conditional-a32.exe*: Ensures that conditional branches in A32 mode are handled correctly
- *test-direct-call-a32.exe*: Ensures that call and return sequences work in A32 mode
- *test-direct-call-t32.exe*: Ensures that transitions (via call) to Thumb mode work correctly
- *test-conditional-mixed.exe*: Ensures that multi-block Thumb functions are handled correctly
- *test-just-exit-t32.exe*: Ensures that Thumb entry points work correctly

# Notes
The *test-just-exit-t32.exe* test is interesting because executables with Thumb entry points have the low bit set (even though it isn't technically the address where the function starts - it happens to work because the ISA clears the bit before jumping). We want to make sure that macaw handles it correctly.
