#include "util.h"

int g;

void __attribute__((noinline)) f2(int x) {
  g = x + 2;
}

void __attribute__((noinline)) f1(int x) {
  f2(x + 1);
}

void _start() {
  g = 0;
  f1(5);
  EXIT();
}
