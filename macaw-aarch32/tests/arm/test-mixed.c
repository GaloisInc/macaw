#include "util.h"

void thumbFunc(int x, int*res) __attribute__((target("thumb")));
void thumbFunc(int x, int* res) {
  if(x > 0) {
    x = x + 10;
  }

  *res = x;
}

void driver(int x, int* res) {
  thumbFunc(x + 1, res);
}

void _start() {
  int i;
  driver((int)&driver, &i);
  EXIT();
}
