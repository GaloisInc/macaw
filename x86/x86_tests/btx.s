.intel_syntax noprefix
.section __TEXT,__text

.global _btc64_addr_reg
_btc64_addr_reg:
	mov rax, 0
	push rax
	popfq
	btc [rdi], rsi
	pushfq
	pop rax
	ret

.global _btr64_addr_reg
_btr64_addr_reg:
	mov rax, 0
	push rax
	popfq
	btr [rdi], rsi
	pushfq
	pop rax
	ret

.global _bts64_addr_reg
_bts64_addr_reg:
	mov rax, 0
	push rax
	popfq
	bts [rdi], rsi
	pushfq
	pop rax
	ret

.global _bts64_addr_imm4
_bts64_addr_imm4:
	mov rax, 0
	push rax
	popfq
	bts QWORD PTR [rdi], 4
	pushfq
	pop rax
	ret

.global _bts64_addr_imm68
_bts64_addr_imm68:
	mov rax, 0
	push rax
	popfq
	bts QWORD PTR [rdi], 68
	pushfq
	pop rax
	ret
