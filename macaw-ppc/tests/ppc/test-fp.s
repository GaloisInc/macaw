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
	stdu 1,-144(1)
	mr 31,1
	xxlxor 32,32,32
	li 9,80
	stxvw4x 32,31,9
	xxlxor 32,32,32
	li 9,96
	stxvw4x 32,31,9
	addis 9,2,.LC0@toc@ha
	addi 9,9,.LC0@toc@l
	lfs 0,0(9)
	stfs 0,48(31)
	addis 9,2,.LC1@toc@ha
	addi 9,9,.LC1@toc@l
	lfs 0,0(9)
	stfs 0,52(31)
	xxlxor 0,0,0
	stfs 0,56(31)
	addi 9,31,80
	std 9,64(31)
	li 9,4
	stw 9,72(31)
	li 9,0
	stw 9,76(31)
	ld 8,64(31)
	lfs 12,48(31)
	lfs 0,52(31)
	stfs 12,112(31)
	lwz 10,112(31)
	stfs 0,112(31)
	lwz 9,112(31)
#APP
 # 14 "test-fp.c" 1
	 stfs    10,0(8)        
 stfs    9,4(8)        
 lfs     9,0(8)        
 lfs     10,4(8)        
 stfsu   10,0(8)        
 stfsu   9,4(8)        
 lfsu    9,-4(8)       
 lfsu    10,4(8)        

 # 0 "" 2
#NO_APP
	stw 10,48(31)
	stw 9,52(31)
	ld 8,64(31)
	lwz 7,72(31)
	lwz 6,76(31)
	lfs 12,48(31)
	lfs 0,52(31)
	stfs 12,112(31)
	lwz 10,112(31)
	stfs 0,112(31)
	lwz 9,112(31)
#APP
 # 26 "test-fp.c" 1
	 stfsx   10,8,7        
 stfsx   9,8,6        
 lfsx    9,8,7        
 lfsx    10,8,6        
 stfsux   10,8,7        
 stfsux   9,8,6        
 lfsux    9,8,7        
 lfsux    10,8,6        

 # 0 "" 2
#NO_APP
	stw 10,48(31)
	stw 9,52(31)
#APP
 # 37 "test-fp.c" 1
	li 0,1
sc
 # 0 "" 2
#NO_APP
	nop
	addi 1,31,144
	ld 31,-8(1)
	blr
	.long 0
	.byte 0,0,0,0,128,1,0,1
	.size	_start,.-.L._start
	.section	.rodata
	.align 2
.LC0:
	.long	1110808986
	.align 2
.LC1:
	.long	1066192077
	.ident	"GCC: (Ubuntu/IBM 5.4.0-6ubuntu1~16.04.1) 5.4.0 20160609"
