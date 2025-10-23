.global test_pop
.syntax unified
.type	test_pop, %function
.thumb
test_pop:
  push {r7}            
  pop {r7}
  mov r0, #1
  bx      lr

.global _start
.syntax unified
_start:
  bl      test_pop
