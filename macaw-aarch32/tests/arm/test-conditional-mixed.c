#include "util.h"

int g = -11;

void __attribute__((noinline, target("thumb"))) f() {
  if(g > 0) {
    g = g + 1;
  }

  g = g - 1090;
}

void _start() {
  // Making this into a call to ensure that the conditional is thumb-ified
  f();
  EXIT();
}
