	.arch armv7-a
	.eabi_attribute 28, 1
	.eabi_attribute 20, 1
	.eabi_attribute 21, 1
	.eabi_attribute 23, 3
	.eabi_attribute 24, 1
	.eabi_attribute 25, 1
	.eabi_attribute 26, 2
	.eabi_attribute 30, 6
	.eabi_attribute 34, 1
	.eabi_attribute 18, 4
	.file	"test-direct-call.c"
	.text
	.global	g
	.bss
	.align	2
	.type	g, %object
	.size	g, 4
g:
	.space	4
	.text
	.align	2
	.global	f2
	.arch armv7-a
	.syntax unified
	.arm
	.fpu vfpv3-d16
	.type	f2, %function
f2:
	@ args = 0, pretend = 0, frame = 8
	@ frame_needed = 1, uses_anonymous_args = 0
	@ link register save eliminated.
	str	fp, [sp, #-4]!
	add	fp, sp, #0
	sub	sp, sp, #12
	str	r0, [fp, #-8]
	ldr	r3, [fp, #-8]
	add	r2, r3, #2
	movw	r3, #:lower16:g
	movt	r3, #:upper16:g
	str	r2, [r3]
	nop
	add	sp, fp, #0
	@ sp needed
	ldr	fp, [sp], #4
	bx	lr
	.size	f2, .-f2
	.align	2
	.global	f1
	.syntax unified
	.arm
	.fpu vfpv3-d16
	.type	f1, %function
f1:
	@ args = 0, pretend = 0, frame = 8
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #8
	str	r0, [fp, #-8]
	ldr	r3, [fp, #-8]
	add	r3, r3, #1
	mov	r0, r3
  cmp r0, #0
	blne	f2
	nop
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
	.size	f1, .-f1
	.align	2
	.global	_start
	.syntax unified
	.arm
	.fpu vfpv3-d16
	.type	_start, %function
_start:
	@ args = 0, pretend = 0, frame = 0
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	movw	r3, #:lower16:g
	movt	r3, #:upper16:g
	mov	r2, #0
	str	r2, [r3]
	mov	r0, #5
	bl	f1
	.syntax divided
@ 16 "test-direct-call.c" 1
	mov     %r7, $1
@ 0 "" 2
@ 16 "test-direct-call.c" 1
	svc #0
@ 0 "" 2
	.arm
	.syntax unified
	nop
	pop	{fp, pc}
	.size	_start, .-_start
	.ident	"GCC: (GNU) 11.2.1 20210728 (Red Hat Cross 11.2.1-1)"
	.section	.note.GNU-stack,"",%progbits
