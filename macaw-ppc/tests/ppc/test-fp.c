#include "util.h"
#include <stdio.h>

void _start() {
  float res [] = {0.0,0.0};
  float a=45.4;
  float *pointer = &res[0];

  asm ( " stw    %0,%1(%2)        \n"
	:
	: "r"(a), "i"(sizeof(int)), "r"(pointer));

  EXIT();
}
