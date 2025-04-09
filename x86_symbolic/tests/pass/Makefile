CC=gcc
CFLAGS=-nostdlib -static -fno-stack-protector
SO_CFLAGS=-nostdlib -fno-stack-protector -fcf-protection=none

unopt = $(patsubst %.c,%.unopt.exe,$(wildcard *.c))
opt = $(patsubst %.c,%.opt.exe,$(wildcard *.c))

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
