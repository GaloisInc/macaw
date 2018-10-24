	.file	"test-imul.c"
	.text
	.globl	g
	.data
	.align 4
	.type	g, @object
	.size	g, 4
g:
	.long	-11
	.text
	.globl	_start
	.type	_start, @function
_start:
.LFB0:
	.cfi_startproc
	pushq	%rbp
	.cfi_def_cfa_offset 16
	.cfi_offset 6, -16
	movq	%rsp, %rbp
	.cfi_def_cfa_register 6
#APP
# 6 "test-imul.c" 1
	mov %edx,0xc(%rsp)
lea (%r12,%rax,1),%ecx
xor %eax,%eax
imul $0xffffffe8,%ebx,%ebx
add %edi,%ebx
mov %edx,%edi

# 0 "" 2
# 14 "test-imul.c" 1
	movq $60,%rax
movq $0,%rdi
syscall
# 0 "" 2
#NO_APP
	nop
	popq	%rbp
	.cfi_def_cfa 7, 8
	ret
	.cfi_endproc
.LFE0:
	.size	_start, .-_start
	.ident	"GCC: (Ubuntu 7.3.0-27ubuntu1~18.04) 7.3.0"
	.section	.note.GNU-stack,"",@progbits
