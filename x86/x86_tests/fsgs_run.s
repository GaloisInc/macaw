// Thi sfile defines functions for getting and setting the fs and gs register
.section __TEXT,__text


.global _pushw_fs
_pushw_fs:
        mov %rsp, %rax
        pushw %fs
        sub %rsp, %rax
        popw (%rdi)
        ret

.global _pushq_fs
_pushq_fs:
        mov %rsp, %rax
        pushq %fs
        sub %rsp, %rax
        popq (%rdi)
        ret

.global _getw_fs
_getw_fs:
        mov $0x123456789abcdef, %rax
        movw %fs, %ax
        ret

.global _getq_fs
_getq_fs:
        movq %fs, %rax
        ret

.global _setw_fs
_setw_fs:
        movw %di, %fs
        ret

.global _setq_fs
_setq_fs:
        movq %rdi, %fs
        ret

// Accessing gs

.global _pushw_gs
_pushw_gs:
        mov %rsp, %rax
        pushw %gs
        sub %rsp, %rax
        popw (%rdi)
        ret

.global _pushq_gs
_pushq_gs:
        mov %rsp, %rax
        pushq %gs
        sub %rsp, %rax
        popq (%rdi)
        ret

.global _getw_gs
_getw_gs:
        // Move constant into %rax so value is more clear.
        mov $0x123456789abcdef, %rax
        movw %gs, %ax
        ret

.global _getq_gs
_getq_gs:
        movq %gs, %rax
        ret

.global _setw_gs
_setw_gs:
        movw %di, %gs
        ret

.global _setq_gs
_setq_gs:
        movq %rdi, %gs
        ret
