# These binaries were obtained from https://musl.cc/
CC64=riscv64-linux-musl-gcc
CC32=riscv32-linux-musl-gcc
CFLAGS=-nostdlib -no-pie -static -fno-stack-protector
SO_CFLAGS=-nostdlib -fno-stack-protector -fcf-protection=none

unopt32 = $(patsubst %.c,%.unopt32.exe,$(wildcard *.c))
unopt64 = $(patsubst %.c,%.unopt64.exe,$(wildcard *.c))
opt32 = $(patsubst %.c,%.opt32.exe,$(wildcard *.c))
opt64 = $(patsubst %.c,%.opt64.exe,$(wildcard *.c))

all: $(unopt32) $(opt32) $(unopt64) $(opt64)

%.unopt32.exe : %.c
	$(CC32) $(CFLAGS) -O0 $< -o $@

%.opt32.exe : %.c
	$(CC32) $(CFLAGS) -O2 $< -o $@

%.unopt64.exe : %.c
	$(CC64) $(CFLAGS) -O0 $< -o $@

%.opt64.exe : %.c
	$(CC64) $(CFLAGS) -O2 $< -o $@

so/libfib.unopt32.so: so/fib.c so/libgetone.unopt32.so
	$(CC32) $(SO_CFLAGS) -O0 -Lso/ -Iso/ -shared $< -lgetone.unopt32 -o $@
so/libfib.opt32.so: so/fib.c so/libgetone.opt32.so
	$(CC32) $(SO_CFLAGS) -O2 -Lso/ -Iso/ -shared $< -lgetone.opt32 -o $@

so/libgetone.unopt32.so : so/getone.c
	$(CC32) $(SO_CFLAGS) -O0 -Iso/ -shared $< -o $@
so/libgetone.opt32.so : so/getone.c
	$(CC32) $(SO_CFLAGS) -O2 -Iso/ -shared $< -o $@

so/so.unopt32.exe : so/so.c so/libfib.unopt32.so
	$(CC32) $(SO_CFLAGS) -O0 -Lso/ -Iso/ $< -lfib.unopt32 -lgetone.unopt32 -o $@
so/so.opt32.exe : so/so.c so/libfib.opt32.so
	$(CC32) $(SO_CFLAGS) -O2 -Lso/ -Iso/ $< -lfib.opt32 -lgetone.opt32 -o $@

so/libfib.unopt64.so: so/fib.c so/libgetone.unopt64.so
	$(CC64) $(SO_CFLAGS) -O0 -Lso/ -Iso/ -shared $< -lgetone.unopt64 -o $@
so/libfib.opt64.so: so/fib.c so/libgetone.opt64.so
	$(CC64) $(SO_CFLAGS) -O2 -Lso/ -Iso/ -shared $< -lgetone.opt64 -o $@

so/libgetone.unopt64.so : so/getone.c
	$(CC64) $(SO_CFLAGS) -O0 -Iso/ -shared $< -o $@
so/libgetone.opt64.so : so/getone.c
	$(CC64) $(SO_CFLAGS) -O2 -Iso/ -shared $< -o $@

so/so.unopt64.exe : so/so.c so/libfib.unopt64.so
	$(CC64) $(SO_CFLAGS) -O0 -Lso/ -Iso/ $< -lfib.unopt64 -lgetone.unopt64 -o $@
so/so.opt64.exe : so/so.c so/libfib.opt64.so
	$(CC64) $(SO_CFLAGS) -O2 -Lso/ -Iso/ $< -lfib.opt64 -lgetone.opt64 -o $@
