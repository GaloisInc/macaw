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
	.file	"test-conditional-call.c"
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
	.global	callee
	.arch armv7-a
	.syntax unified
	.arm
	.fpu vfpv3-d16
	.type	callee, %function
callee:
	@ args = 0, pretend = 0, frame = 8
	@ frame_needed = 1, uses_anonymous_args = 0
	@ link register save eliminated.
	str	fp, [sp, #-4]!
	add	fp, sp, #0
	sub	sp, sp, #12
	str	r0, [fp, #-8]
	ldr	r3, [fp, #-8]
	cmp	r3, #0
	bne	.L3
	movw	r3, #:lower16:g
	movt	r3, #:upper16:g
	mov	r2, #1
	str	r2, [r3]
.L3:
	nop
	add	sp, fp, #0
	@ sp needed
	ldr	fp, [sp], #4
	bx	lr
	.size	callee, .-callee
	.align	2
	.global	test_conditional_call
	.syntax unified
	.arm
	.fpu vfpv3-d16
	.type	test_conditional_call, %function
test_conditional_call:
	@ args = 0, pretend = 0, frame = 8
	@ frame_needed = 1, uses_anonymous_args = 0
	push	{fp, lr}
	add	fp, sp, #4
	sub	sp, sp, #8
	str	r0, [fp, #-8]
	movw	r3, #:lower16:g
	movt	r3, #:upper16:g
	mov	r2, #100
	str	r2, [r3]
	ldr	r3, [fp, #-8]
	cmp	r3, #0
	bne	.L5
	movw	r3, #:lower16:g
	movt	r3, #:upper16:g
	mvn	r2, #4
	str	r2, [r3]
.L5:
	ldr	r0, [fp, #-8]
  cmp r0, #0
	bleq	callee
	movw	r3, #:lower16:g
	movt	r3, #:upper16:g
	ldr	r3, [r3]
	cmp	r3, #0
	movgt	r3, #1
	movle	r3, #0
	uxtb	r3, r3
	mov	r0, r3
	sub	sp, fp, #4
	@ sp needed
	pop	{fp, pc}
	.size	test_conditional_call, .-test_conditional_call
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
	bl	test_conditional_call
	.syntax divided
@ 26 "test-conditional-call.c" 1
	mov     %r7, $1
@ 0 "" 2
@ 26 "test-conditional-call.c" 1
	svc #0
@ 0 "" 2
	.arm
	.syntax unified
	nop
	pop	{fp, pc}
	.size	_start, .-_start
	.ident	"GCC: (GNU) 11.2.1 20210728 (Red Hat Cross 11.2.1-1)"
	.section	.note.GNU-stack,"",%progbits
