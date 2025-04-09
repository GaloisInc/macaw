	.file	"test-direct-calls.c"
	.machine ppc
	.section	".text"
	.comm	g1,4,4
	.comm	g2,4,4
	.comm	g3,4,4
	.comm	g4,4,4
	.align 2
	.globl f2
	.type	f2, @function
f2:
.LFB0:
	.cfi_startproc
	stwu 1,-16(1)
	.cfi_def_cfa_offset 16
	stw 31,12(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	lis 9,g2@ha
	la 9,g2@l(9)
	mr 3,9
	addi 11,31,16
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE0:
	.size	f2,.-f2
	.align 2
	.globl f1
	.type	f1, @function
f1:
.LFB1:
	.cfi_startproc
	stwu 1,-48(1)
	.cfi_def_cfa_offset 48
	mflr 0
	stw 0,52(1)
	stw 30,40(1)
	stw 31,44(1)
	.cfi_offset 65, 4
	.cfi_offset 30, -8
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	stw 3,24(31)
	stw 4,28(31)
	stw 5,32(31)
	lis 9,g1@ha
	la 9,g1@l(9)
	stw 9,8(31)
	lwz 10,24(31)
	lwz 9,8(31)
	add 10,10,9
	lwz 9,28(31)
	add 9,10,9
	lwz 10,32(31)
	add 9,10,9
	stw 9,8(31)
	lwz 9,32(31)
	slwi 9,9,1
	stw 9,8(31)
	lwz 9,28(31)
	addi 30,9,-100
	bl f2
	mr 9,3
	add 9,30,9
	lwz 10,8(31)
	subf 9,9,10
	stw 9,8(31)
	lwz 9,8(31)
	mr 3,9
	addi 11,31,48
	lwz 0,4(11)
	mtlr 0
	lwz 30,-8(11)
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_restore 30
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE1:
	.size	f1,.-f1
	.align 2
	.globl _start
	.type	_start, @function
_start:
.LFB2:
	.cfi_startproc
	stwu 1,-32(1)
	.cfi_def_cfa_offset 32
	mflr 0
	stw 0,36(1)
	stw 31,28(1)
	.cfi_offset 65, 4
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	lis 9,g1@ha
	la 9,g1@l(9)
	stw 9,8(31)
	lis 9,g2@ha
	la 9,g2@l(9)
	stw 9,12(31)
	lis 9,g3@ha
	la 9,g3@l(9)
	stw 9,16(31)
	lwz 5,16(31)
	lwz 4,12(31)
	lwz 3,8(31)
	bl f1
	mr 10,3
	lis 9,g1@ha
	stw 10,g1@l(9)
#APP
 # 25 "test-direct-calls.c" 1
	li 0,1
sc
 # 0 "" 2
#NO_APP
	nop
	addi 11,31,32
	lwz 0,4(11)
	mtlr 0
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE2:
	.size	_start,.-_start
	.ident	"GCC: (Ubuntu 8.4.0-3ubuntu1) 8.4.0"
	.section	.note.GNU-stack,"",@progbits
