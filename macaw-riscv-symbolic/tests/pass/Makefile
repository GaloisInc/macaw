# These binaries were obtained from https://musl.cc/
CC64=riscv64-linux-musl-gcc
CC32=riscv32-linux-musl-gcc
CFLAGS=-nostdlib -no-pie -static -fno-stack-protector

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
