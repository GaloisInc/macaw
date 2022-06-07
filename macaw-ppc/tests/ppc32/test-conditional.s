	.file	"test-conditional.c"
	.machine ppc
	.section	".text"
	.globl g
	.section	.sdata,"aw"
	.align 2
	.type	g, @object
	.size	g, 4
g:
	.long	-11
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
	lis 9,g@ha
	lwz 9,g@l(9)
	cmpwi 7,9,0
	ble 7,.L2
	lis 9,g@ha
	lwz 9,g@l(9)
	addi 10,9,1
	lis 9,g@ha
	stw 10,g@l(9)
.L2:
#APP
 # 10 "test-conditional.c" 1
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
