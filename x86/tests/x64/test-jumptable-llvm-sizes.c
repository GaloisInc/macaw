// End-to-end test for the .llvm_jump_table_sizes section emitted by Clang
// (>= 20) under -mllvm -emit-jump-table-sizes-section. The Makefile rule
// passes that flag and links no-pie so the section's R_X86_64_64 entries
// resolve to literal addresses (the parser reads raw bytes).
//
// The no-pie link is load-bearing: with a PIE (ET_DYN) binary the parser
// does not error out, but it also does not work. The static linker leaves
// the section's R_X86_64_64 entries as load-time relocations, so the raw
// on-disk bytes are addends rather than final absolute addresses. On top of
// that, llvmJumpTableSizesFromElf resolves addresses via resolveAbsoluteAddr,
// which is hardcoded to region 0, whereas macaw loads ET_DYN binaries into
// region 1 (see adjustedLoadRegionIndex). So every entry would come back as
// an UnresolvableAddress warning and the size map would be empty; discovery
// would then fall back to its own analysis. Supporting PIE binaries is future
// work: it would require applying the section's relocations rather than
// trusting raw bytes, and resolving against the region the section actually
// loads into rather than region 0.
//
// Each case body calls a distinct externally-defined function so the
// compiler cannot collapse the switch into a constant lookup table — the
// only viable lowering for irregular control flow at this case count is a
// real jump table. The switch index is laundered through a volatile read
// so macaw's abstract-interpretation pass cannot bound it on its own —
// making the externally-supplied size load-bearing for classification.

#include "util.h"

volatile int idx;
volatile int sink;

// Defined below in inline asm so they can't be inlined or analyzed away.
int ext0(int);
int ext1(int);
int ext2(int);
int ext3(int);
int ext4(int);
int ext5(int);
int ext6(int);
int ext7(int);

int handler(int x, int v) {
    switch (x) {
    case 0: return ext0(v);
    case 1: return ext1(v);
    case 2: return ext2(v);
    case 3: return ext3(v);
    case 4: return ext4(v);
    case 5: return ext5(v);
    case 6: return ext6(v);
    case 7: return ext7(v);
    default: __builtin_unreachable();
    }
}

#define EXTFN(name, k) \
    asm(".globl " #name "\n" \
        #name ":\n" \
        "  lea " #k "(%rdi), %eax\n" \
        "  ret\n")
EXTFN(ext0, 0x10);
EXTFN(ext1, 0x21);
EXTFN(ext2, 0x32);
EXTFN(ext3, 0x43);
EXTFN(ext4, 0x54);
EXTFN(ext5, 0x65);
EXTFN(ext6, 0x76);
EXTFN(ext7, 0x07);

void _start() {
    sink = handler(idx, idx);
    EXIT();
}
