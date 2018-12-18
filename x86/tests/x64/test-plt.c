// This is a simple call to puts to test that we resolve the PLT stub
// to puts.
//
// It should be compiled with
//   `clang -fpic -FPIC -o test-plt.exe test-plc.c`
#include <stdio.h>

int main(int argc, char** argv) {
    puts("Hello World");
}
