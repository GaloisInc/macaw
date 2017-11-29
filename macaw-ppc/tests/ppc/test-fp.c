#include "util.h"
#include <stdio.h>

void _start() {
  float res [] = {0.0,0.0};
  float a=45.4; // r9
  float b=1.1;
  float *pointer = &res[0]; // r10

  /* TEST: Load/store single precision */
  asm ( " stfs    %1,0(%2)        \n"
	: "=r"(b)
	: "r"(a), "r"(pointer));

  EXIT();
}
