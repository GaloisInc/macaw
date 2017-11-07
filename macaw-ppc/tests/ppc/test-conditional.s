	.file	"test-conditional.c"
	.globl g
	.section	".data"
	.align 2
	.type	g, @object
	.size	g, 4
g:
	.long	-11
	.section	".text"
	.align 2
	.globl _start
	.section	".opd","aw"
	.align 3
_start:
	.quad	.L._start,.TOC.@tocbase,0
	.previous
	.type	_start, @function
.L._start:
	std 31,-8(1)
	stdu 1,-64(1)
	mr 31,1
	addis 9,2,g@toc@ha
	addi 9,9,g@toc@l
	lwa 9,0(9)
	cmpwi 7,9,0
	ble 7,.L2
	addis 9,2,g@toc@ha
	addi 9,9,g@toc@l
	lwa 9,0(9)
	addi 9,9,1
	extsw 10,9
	addis 9,2,g@toc@ha
	addi 9,9,g@toc@l
	stw 10,0(9)
.L2:
#APP
 # 10 "test-conditional.c" 1
	li 0,1
sc
 # 0 "" 2
#NO_APP
	nop
	addi 1,31,64
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,0,128,1,0,1
	.size	_start,.-.L._start
	.ident	"GCC: (Ubuntu 7.2.0-6ubuntu1) 7.2.0"
