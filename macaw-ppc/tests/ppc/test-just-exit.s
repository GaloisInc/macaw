	.file	"test-just-exit.c"
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
	stdu 1,-64(1)
	mr 31,1
#APP
 # 4 "test-just-exit.c" 1
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
	.ident	"GCC: (Ubuntu/IBM 5.4.0-6ubuntu1~16.04.1) 5.4.0 20160609"
