        .text
        .globl _start
_start:
        movq %rsp, %rax
        subq $64, %rsp
        andq $-32, %rsp
        movq %rax, 32(%rsp)

        movq 32(%rsp), %rsi
        leaq (%rsi), %rsp

        movq $60, %rax
        syscall
        nop
        ret
