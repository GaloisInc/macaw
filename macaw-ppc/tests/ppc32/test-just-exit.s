	.file	"test-just-exit.c"
	.machine ppc
	.section	".text"
	.align 2
	.globl _start
	.type	_start, @function
_start:
.LFB0:
	.cfi_startproc
	stwu 1,-16(1)
	.cfi_def_cfa_offset 16
	stw 31,12(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
#APP
 # 4 "test-just-exit.c" 1
	li 0,1
sc
 # 0 "" 2
#NO_APP
	nop
	addi 11,31,16
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE0:
	.size	_start,.-_start
	.ident	"GCC: (Ubuntu 8.4.0-3ubuntu1) 8.4.0"
	.section	.note.GNU-stack,"",@progbits
