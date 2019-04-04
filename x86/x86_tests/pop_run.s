.intel_syntax noprefix
.section __TEXT,__text

// This function tests what happens when we pop into rsp
.global _pop_rsp
_pop_rsp:
	push rbp
	mov rbp, rsp
	sub rsp, 0x100
	mov QWORD PTR [rsp], rdi
	// Pop into rsp.  This should assign rsp the value currently stored in rsp.
	pop rsp
	mov [rsi], rsp
	mov rsp, rbp
	pop rbp
	ret

	// pop_sp(v, &rsp0, &rsp1) tests what happens when poping into sp at an address
	// that should make the increment visible.
.global _pop_sp
_pop_sp:
	// Save stack pointer in rbp
	push rbp
	mov rbp, rsp
	// Give some space to the stack
	sub rsp, 0x100
	// Decrease rsp and make sure the low 16-bits are 0xffff
	and rsp, 0xffffffffffff0000
	sub rsp, 1
	// Store rsp in [rsi] (2nd argument)
	mov [rsi], rsp
	// Move rdi (first argument) into address pointed by rsp
	// This is used to have a known value poped from rsp.
	mov QWORD PTR [rsp], rdi
	// Pop into sp.  This should increment rsp, and store the value currently stored in [rsp] in sp.
	pop sp
	// Store new stack pointer in address pointed to by rdx (3rd argument)
	mov [rdx], rsp
	// Restore rsp,rbp, and return
	mov rsp, rbp
	pop rbp
	ret
