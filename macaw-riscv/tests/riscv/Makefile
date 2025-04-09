# These binaries were obtained from https://musl.cc/
CC64=riscv64-linux-musl-gcc
CC32=riscv32-linux-musl-gcc
CFLAGS=-nostdlib -no-pie -static -fno-stack-protector
CFLAGS_DYNAMIC=-nostartfiles -fno-stack-protector

rv32gc = $(patsubst %.c,%-rv32gc.exe,$(wildcard *.c))
rv64gc = $(patsubst %.c,%-rv64gc.exe,$(wildcard *.c))

all: $(rv32gc) $(rv64gc)

%-rv32gc.exe : %.c
	$(CC32) $(CFLAGS) -O0 $< -o $@

%-rv64gc.exe : %.c
	$(CC32) $(CFLAGS) -O0 $< -o $@

# This test relies on the binary having dynamic relocations.
relocs-rv32gc.exe: relocs.c
	$(CC32) $(CFLAGS_DYNAMIC) $< -o $@

relocs-rv64gc.exe: relocs.c
	$(CC64) $(CFLAGS_DYNAMIC) $< -o $@
