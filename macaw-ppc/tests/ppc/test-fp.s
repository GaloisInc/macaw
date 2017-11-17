	.file	"test-fp.c"
	.machine power7
	.section	".toc","aw"
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
	stdu 1,-96(1)
	mr 31,1
	xxlxor 0,0,0
	stfs 0,64(31)
	xxlxor 0,0,0
	stfs 0,68(31)
	addis 9,2,.LC0@toc@ha
	addi 9,9,.LC0@toc@l
	lfs 0,0(9)
	stfs 0,48(31)
	addi 9,31,64
	std 9,56(31)
	lwz 9,48(31)
	ld 10,56(31)
#APP
 # 9 "test-fp.c" 1
	 stw    9,4(10)        

 # 0 "" 2
 # 13 "test-fp.c" 1
	li 0,1
sc
 # 0 "" 2
#NO_APP
	nop
	addi 1,31,96
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,0,128,1,0,1
	.size	_start,.-.L._start
	.section	.rodata
	.align 2
.LC0:
	.long	1110808986
	.ident	"GCC: (Ubuntu/IBM 5.4.0-6ubuntu1~16.04.1) 5.4.0 20160609"
