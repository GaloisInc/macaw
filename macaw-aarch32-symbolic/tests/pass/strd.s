  .global test_strd
  .syntax unified
test_strd:
  push    {fp}            @ (str fp, [sp, #-4]!)
  add     fp, sp, #0
  movw    r3, #312        @ 0x138
  movt    r3, #2
  mov     r0, #42 @ 0x2a
  mov     r1, #0
  strd    r0, [r3]
  movw    r3, #312        @ 0x138
  movt    r3, #2
  ldrd    r2, [r3]
  cmp     r3, #0
  cmpeq   r2, #42 @ 0x2a
  moveq   r3, #1
  movne   r3, #0
  uxtb    r3, r3
  mov     r0, r3
  add     sp, fp, #0
  pop     {fp}            @ (ldr fp, [sp], #4)
  bx      lr

  .global _start
  .syntax unified
_start:
  push    {fp, lr}
  add     fp, sp, #4
  bl      test_strd
  nop     {0}
  pop     {fp, pc}
