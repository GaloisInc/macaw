.intel_syntax noprefix
.section __TEXT,__text

.global _do_ucomiss
_do_ucomiss:
	mov rax, 0
	push rax
	popfq
	ucomiss xmm0, xmm1
	pushfq
	pop rax
	ret

.global _get_mxcsr
_get_mxcsr:
	push rax
	stmxcsr [rsp]
	pop rax
	ret
.global _set_mxcsr
_set_mxcsr:
	push rdi
	ldmxcsr [rsp]
	pop rdi
	ret
