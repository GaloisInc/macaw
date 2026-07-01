CC=gcc
CFLAGS=-nostdlib -static -fno-stack-protector
SO_CFLAGS=-nostdlib -fno-stack-protector -fcf-protection=none

unopt = $(patsubst %.c,%.unopt.exe,$(wildcard *.c))
opt = $(patsubst %.c,%.opt.exe,$(wildcard *.c))

# This test requires clang -fPIC to produce a PIC-relative jump table;
# gcc -O2 optimizes the switch into a plain increment loop instead.
switch-jump-table.opt.exe: switch-jump-table.c
	clang $(CFLAGS) -O2 -fno-unroll-loops -fPIC $< -o $@

# This test requires clang -O2 to lower the switch to a jump table gated by
# 32-bit comparisons on the argument register; gcc -O2 emits a plain byte
# comparison with no table, which does not exercise the abstract domain.
switch-jump-table-abs.opt.exe: switch-jump-table-abs.c
	clang $(CFLAGS) -O2 -fno-pic $< -o $@

all: $(unopt) $(opt)

%.unopt.exe : %.c
	$(CC) $(CFLAGS) -O0 $< -o $@

%.opt.exe : %.c
	$(CC) $(CFLAGS) -O2 $< -o $@

so/libfib.unopt.so: so/fib.c so/libgetone.unopt.so
	$(CC) $(SO_CFLAGS) -O0 -Lso/ -Iso/ -shared $< -lgetone.unopt -o $@
so/libfib.opt.so: so/fib.c so/libgetone.opt.so
	$(CC) $(SO_CFLAGS) -O2 -Lso/ -Iso/ -shared $< -lgetone.opt -o $@

so/libgetone.unopt.so : so/getone.c
	$(CC) $(SO_CFLAGS) -O0 -Iso/ -shared $< -o $@
so/libgetone.opt.so : so/getone.c
	$(CC) $(SO_CFLAGS) -O2 -Iso/ -shared $< -o $@

so/so.unopt.exe : so/so.c so/libfib.unopt.so
	$(CC) $(SO_CFLAGS) -O0 -Lso/ -Iso/ $< -lfib.unopt -lgetone.unopt -o $@
so/so.opt.exe : so/so.c so/libfib.opt.so
	$(CC) $(SO_CFLAGS) -O2 -Lso/ -Iso/ $< -lfib.opt -lgetone.opt -o $@
