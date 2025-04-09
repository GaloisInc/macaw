	.file	"test-direct-calls.c"
	.comm	g1,4,4
	.comm	g2,4,4
	.comm	g3,4,4
	.comm	g4,4,4
	.section	".toc","aw"
	.align 3
.LC0:
	.quad	g2
	.section	".text"
	.align 2
	.globl f2
	.section	".opd","aw"
	.align 3
f2:
	.quad	.L.f2,.TOC.@tocbase,0
	.previous
	.type	f2, @function
.L.f2:
	std 31,-8(1)
	stdu 1,-64(1)
	mr 31,1
	addis 9,2,.LC0@toc@ha
	ld 9,.LC0@toc@l(9)
	extsw 9,9
	mr 3,9
	addi 1,31,64
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,0,128,1,0,1
	.size	f2,.-.L.f2
	.section	".toc","aw"
.LC1:
	.quad	g1
	.section	".text"
	.align 2
	.globl f1
	.section	".opd","aw"
	.align 3
f1:
	.quad	.L.f1,.TOC.@tocbase,0
	.previous
	.type	f1, @function
.L.f1:
	mflr 0
	std 0,16(1)
	std 30,-16(1)
	std 31,-8(1)
	stdu 1,-144(1)
	mr 31,1
	std 3,192(31)
	std 4,200(31)
	std 5,208(31)
	addis 9,2,.LC1@toc@ha
	ld 9,.LC1@toc@l(9)
	std 9,112(31)
	ld 10,192(31)
	ld 9,112(31)
	add 10,10,9
	ld 9,200(31)
	add 9,10,9
	ld 10,208(31)
	add 9,10,9
	std 9,112(31)
	ld 9,208(31)
	sldi 9,9,1
	std 9,112(31)
	ld 9,200(31)
	addi 30,9,-100
	bl f2
	mr 9,3
	add 9,30,9
	ld 10,112(31)
	subf 9,9,10
	std 9,112(31)
	ld 9,112(31)
	extsw 9,9
	mr 3,9
	addi 1,31,144
	ld 0,16(1)
	mtlr 0
	ld 30,-16(1)
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,1,128,2,0,1
	.size	f1,.-.L.f1
	.section	".toc","aw"
	.set .LC2,.LC1
	.set .LC3,.LC0
.LC4:
	.quad	g3
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
	mflr 0
	std 0,16(1)
	std 30,-16(1)
	std 31,-8(1)
	stdu 1,-160(1)
	mr 31,1
	addis 30,2,.LC2@toc@ha
	ld 9,.LC2@toc@l(30)
	std 9,112(31)
	addis 9,2,.LC3@toc@ha
	ld 9,.LC3@toc@l(9)
	std 9,120(31)
	addis 9,2,.LC4@toc@ha
	ld 9,.LC4@toc@l(9)
	std 9,128(31)
	ld 5,128(31)
	ld 4,120(31)
	ld 3,112(31)
	bl f1
	mr 9,3
	mr 10,9
	ld 9,.LC2@toc@l(30)
	stw 10,0(9)
#APP
 # 25 "test-direct-calls.c" 1
	li 0,1
sc
 # 0 "" 2
#NO_APP
	nop
	addi 1,31,160
	ld 0,16(1)
	mtlr 0
	ld 30,-16(1)
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,1,128,2,0,1
	.size	_start,.-.L._start
	.ident	"GCC: (Ubuntu 7.2.0-6ubuntu1) 7.2.0"
