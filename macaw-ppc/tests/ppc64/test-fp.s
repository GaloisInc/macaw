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
	stdu 1,-256(1)
	mr 31,1
	li 9,0
	std 9,116(31)
	li 9,0
	std 9,124(31)
	li 9,0
	std 9,132(31)
	li 9,0
	std 9,140(31)
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
	addi 9,31,116
	std 9,64(31)
	li 9,0
	std 9,152(31)
	li 9,0
	std 9,160(31)
	li 9,0
	std 9,168(31)
	li 9,0
	std 9,176(31)
	li 9,0
	std 9,184(31)
	li 9,0
	std 9,192(31)
	li 9,0
	std 9,200(31)
	li 9,0
	std 9,208(31)
	addis 9,2,.LC2@toc@ha
	addi 9,9,.LC2@toc@l
	lfd 0,0(9)
	stfd 0,72(31)
	addis 9,2,.LC3@toc@ha
	addi 9,9,.LC3@toc@l
	lfd 0,0(9)
	stfd 0,80(31)
	xxlxor 0,0,0
	stfd 0,88(31)
	addi 9,31,152
	std 9,96(31)
	li 9,4
	stw 9,104(31)
	li 9,0
	stw 9,108(31)
	li 9,8
	stw 9,112(31)
	ld 8,64(31)
	lfs 12,48(31)
	lfs 0,52(31)
	stfs 12,224(31)
	lwz 10,224(31)
	stfs 0,224(31)
	lwz 9,224(31)
#APP
 # 20 "test-fp.c" 1
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
	lwz 7,104(31)
	lwz 6,108(31)
	lfs 12,48(31)
	lfs 0,52(31)
	stfs 12,224(31)
	lwz 10,224(31)
	stfs 0,224(31)
	lwz 9,224(31)
#APP
 # 32 "test-fp.c" 1
	 stfsx   10,8,7        
 stfsx   9,8,6        
 lfsx    9,8,7        
 lfsx    10,8,6        
 stfsux  10,8,7        
 stfsux  9,8,6        
 lfsux   9,8,7        
 lfsux   10,8,6        

 # 0 "" 2
#NO_APP
	stw 10,48(31)
	stw 9,52(31)
	ld 8,96(31)
	lfd 12,72(31)
	lfd 0,80(31)
	stfd 12,232(31)
	ld 10,232(31)
	stfd 0,232(31)
	ld 9,232(31)
#APP
 # 44 "test-fp.c" 1
	 stfd    10,0(8)        
 stfd    9,4(8)        
 lfd     9,0(8)        
 lfd     10,4(8)        
 stfdu   10,0(8)        
 stfdu   9,4(8)        
 lfdu    9,-4(8)       
 lfdu    10,4(8)        

 # 0 "" 2
#NO_APP
	std 10,72(31)
	std 9,80(31)
	ld 8,96(31)
	lwz 7,112(31)
	lwz 6,108(31)
	lfd 12,72(31)
	lfd 0,80(31)
	stfd 12,232(31)
	ld 10,232(31)
	stfd 0,232(31)
	ld 9,232(31)
#APP
 # 56 "test-fp.c" 1
	 stfdx   10,8,7        
 stfdx   9,8,6        
 lfdx    9,8,7        
 lfdx    10,8,6        
 stfdux  10,8,7        
 stfdux  9,8,6        
 lfdux   9,8,7        
 lfdux   10,8,6        

 # 0 "" 2
#NO_APP
	std 10,72(31)
	std 9,80(31)
#APP
 # 67 "test-fp.c" 1
	li 0,1
sc
 # 0 "" 2
#NO_APP
	nop
	addi 1,31,256
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
	.align 3
.LC2:
	.long	1078238281
	.long	3126736191
	.align 3
.LC3:
	.long	1076246755
	.long	1760592994
	.ident	"GCC: (Ubuntu/IBM 5.4.0-6ubuntu1~16.04.1) 5.4.0 20160609"
