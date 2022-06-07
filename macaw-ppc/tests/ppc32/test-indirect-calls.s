	.file	"test-indirect-calls.c"
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
	stwu 1,-32(1)
	.cfi_def_cfa_offset 32
	stw 31,28(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	stw 3,8(31)
	lis 9,g2@ha
	la 9,g2@l(9)
	mr 3,9
	addi 11,31,32
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
	stw 31,44(1)
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	stw 3,24(31)
	lis 9,g1@ha
	la 9,g1@l(9)
	stw 9,8(31)
	lwz 10,8(31)
	lwz 9,24(31)
	add 9,10,9
	stw 9,8(31)
	lwz 9,8(31)
	mr 3,9
	addi 11,31,48
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
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
	stw 9,12(31)
	lis 9,g2@ha
	la 9,g2@l(9)
	stw 9,16(31)
	lis 9,g3@ha
	la 9,g3@l(9)
	stw 9,20(31)
	lis 9,f1@ha
	la 9,f1@l(9)
	stw 9,8(31)
	lwz 10,12(31)
	lwz 9,16(31)
	cmpw 7,10,9
	ble 7,.L6
	lis 9,f2@ha
	la 9,f2@l(9)
	stw 9,8(31)
.L6:
	lwz 10,20(31)
	lwz 9,16(31)
	add 10,10,9
	lwz 9,8(31)
	mr 3,10
	mtctr 9
	bctrl
	mr 10,3
	lis 9,g1@ha
	stw 10,g1@l(9)
#APP
 # 27 "test-indirect-calls.c" 1
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
