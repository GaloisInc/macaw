  .syntax unified
  .global syscall
syscall:
  mov ip, sp
  push {r4, r5, r6, r7}
  mov r7, r0
  mov r0, r1
  mov r1, r2
  mov r2, r3
  ldm ip, {r3, r4, r5, r6}
  svc 0x0
  pop {r4, r5, r6, r7}
  cmn r0, #4096
  bxcc lr
  b __syscall_error

__syscall_error:
  rsb r0, r0, #0
  mov r1, r0
  mov r2, lr
  mvn r0, #61440
  mov lr, pc
  sub pc, r0, #31
  mov lr, r2
  ldr r2, [pc, #12]
  ldr r2, [pc, r2]
  str r1, [r0, r2]
  mvn r0, #0
  bx lr
.4byte 0x00010018
