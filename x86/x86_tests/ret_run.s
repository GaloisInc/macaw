.intel_syntax noprefix
.section __TEXT,__text

.global _ret_noimm
.global _ret_noimm_ret
_ret_noimm:
	// Save rsp to rbp
	push rbp
	mov rbp, rsp
	// Subtract 10 from rsp to have some space
	sub rsp,0x10
	// Call function for returning
	call _ret_noimm_tgt
_ret_noimm_ret:
	// Store rsp post return in third argument
	mov [rdx], rsp
	// Restore rsp
	mov rsp, rbp
	pop rbp
	ret
_ret_noimm_tgt:
	mov [rsi], rsp
	mov rcx, [rsp]
	mov [rdi], rcx
	ret

.global _ret_imm8
.global _ret_imm8_ret
_ret_imm8:
	// Save rsp to rbp
	push rbp
	mov rbp, rsp
	// Subtract 10 from rsp to have some space
	sub rsp,0x18
	// Call function for returning
	call _ret_imm8_tgt
_ret_imm8_ret:
	// Store rsp post return in third argument
	mov [rdx], rsp
	// Restore rsp
	mov rsp, rbp
	pop rbp
	ret
_ret_imm8_tgt:
	mov [rsi], rsp
	mov rcx, [rsp]
	mov [rdi], rcx
	ret 8


.global _ret_imm8000
.global _ret_imm8000_ret
_ret_imm8000:
	// Save rsp to rbp
	push rbp
	mov rbp, rsp
	// Subtract 10 from rsp to have some space
	sub rsp,0x8000
	// Call function for returning
	call _ret_imm8000_tgt
_ret_imm8000_ret:
	// Store rsp post return in third argument
	mov [rdx], rsp
	// Restore rsp
	mov rsp, rbp
	pop rbp
	ret
_ret_imm8000_tgt:
	mov [rsi], rsp
	mov rcx, [rsp]
	mov [rdi], rcx
	ret 0x8000

.global _ret_imm10000
.global _ret_imm10000_ret
_ret_imm10000:
	// Save rsp to rbp
	push rbp
	mov rbp, rsp
	// Subtract 10 from rsp to have some space
	sub rsp,0x10000
	// Call function for returning
	call _ret_imm10000_tgt
_ret_imm10000_ret:
	// Store rsp post return in third argument
	mov [rdx], rsp
	// Restore rsp
	mov rsp, rbp
	pop rbp
	ret
_ret_imm10000_tgt:
	mov [rsi], rsp
	mov rcx, [rsp]
	mov [rdi], rcx
	ret 0x10000
