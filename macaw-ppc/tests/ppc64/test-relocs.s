	.file	"test-relocs.c"
	.section	".text"
	.section	.rodata
	.align 3
.LC0:
	.string	"World"
	.align 3
.LC1:
	.string	"Hello, %s!\n"
	.section	".text"
	.align 2
	.globl main
	.section	".opd","aw"
	.align 3
main:
	.quad	.L.main,.TOC.@tocbase,0
	.previous
	.type	main, @function
.L.main:
.LFB0:
	.cfi_startproc
	mflr 0
	std 0,16(1)
	std 31,-8(1)
	stdu 1,-128(1)
	.cfi_def_cfa_offset 128
	.cfi_offset 65, 16
	.cfi_offset 31, -8
	mr 31,1
	.cfi_def_cfa_register 31
	addis 4,2,.LC0@toc@ha
	addi 4,4,.LC0@toc@l
	addis 3,2,.LC1@toc@ha
	addi 3,3,.LC1@toc@l
	bl printf
	nop
	li 9,0
	mr 3,9
	addi 1,31,128
	.cfi_def_cfa 1, 0
	ld 0,16(1)
	mtlr 0
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,1,128,1,0,1
	.cfi_endproc
.LFE0:
	.size	main,.-.L.main
	.ident	"GCC: (Ubuntu 9.4.0-1ubuntu1~20.04) 9.4.0"
