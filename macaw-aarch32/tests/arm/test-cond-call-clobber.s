        .arch armv7-a
        .syntax unified
        .arm

        .global _start
        .type   _start, %function
_start:
        mov     r0, #5
        bl      caller
        mov     r7, #1
        svc     #0
        .size   _start, .-_start

        .global callee
        .type   callee, %function
callee:
        mov     r2, #42         @ clobbers caller-saved r2
        bx      lr
        .size   callee, .-callee

        .global caller
        .type   caller, %function
caller:
        push    {fp, lr}
        add     fp, sp, #4
        mov     r2, #100        @ caller's r2 = 100
        cmp     r0, #0
        bleq    callee          @ predicated call
post_call:
        mov     r0, r2          @ r2 may be 42 (call taken) or 100 (call not taken)
        pop     {fp, pc}
        .size   caller, .-caller
