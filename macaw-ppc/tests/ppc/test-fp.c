#include "util.h"
#include <stdio.h>

void _start() {
  float res [] = {0.0,0.0,0.0,0.0,0.0,0.0,0.0,0.0};
  float a=45.4; // r9
  float b=1.1;  // r10
  float c=0.0;
  float *pointer = &res[0]; // r10
  int idx1 = 4;
  int idx2 = 0;
  
  /* TEST: Load/store single precision D-form */
  asm ( " stfs    %0,0(%2)        \n"
	" stfs    %1,4(%2)        \n"
	" lfs     %1,0(%2)        \n"
	" lfs     %0,4(%2)        \n"
	" stfsu   %0,0(%2)        \n"
	" stfsu   %1,4(%2)        \n"
	" lfsu    %1,-4(%2)       \n"
	" lfsu    %0,4(%2)        \n"
	: "+r"(a), "+r"(b)
	: "r"(pointer));

  /* TEST: Load/store single precision X-form */
  asm ( " stfsx   %0,%2,%3        \n"
	" stfsx   %1,%2,%4        \n"
	" lfsx    %1,%2,%3        \n"
	" lfsx    %0,%2,%4        \n"
	" stfsux   %0,%2,%3        \n"
	" stfsux   %1,%2,%4        \n"
	" lfsux    %1,%2,%3        \n"
	" lfsux    %0,%2,%4        \n"
	: "+r"(a), "+r"(b)
	: "r"(pointer), "r"(idx1), "r"(idx2));

  EXIT();
}
