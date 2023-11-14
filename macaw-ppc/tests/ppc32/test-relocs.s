	.file	"test-relocs.c"
	.machine ppc
	.section	".text"
	.section	.rodata
	.align 2
.LC0:
	.string	"World"
	.align 2
.LC1:
	.string	"Hello, %s!\n"
	.section	".text"
	.align 2
	.globl main
	.type	main, @function
main:
.LFB0:
	.cfi_startproc
	stwu 1,-16(1)
	.cfi_def_cfa_offset 16
	mflr 0
	stw 0,20(1)
	stw 31,12(1)
	.cfi_offset 65, 4
	.cfi_offset 31, -4
	mr 31,1
	.cfi_def_cfa_register 31
	lis 9,.LC0@ha
	la 4,.LC0@l(9)
	lis 9,.LC1@ha
	la 3,.LC1@l(9)
	crxor 6,6,6
	bl printf
	li 9,0
	mr 3,9
	addi 11,31,16
	lwz 0,4(11)
	mtlr 0
	lwz 31,-4(11)
	.cfi_def_cfa 11, 0
	mr 1,11
	.cfi_restore 31
	.cfi_def_cfa_register 1
	blr
	.cfi_endproc
.LFE0:
	.size	main,.-main
	.ident	"GCC: (Ubuntu 8.4.0-3ubuntu1) 8.4.0"
	.section	.note.GNU-stack,"",@progbits
