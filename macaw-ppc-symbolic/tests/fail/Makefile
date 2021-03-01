CC64=powerpc64-linux-gnu-gcc
CC32=powerpc-linux-gnu-gcc
CFLAGS=-nostdlib -static -fno-stack-protector

unopt32 = $(patsubst %.c,%.unopt32.exe,$(wildcard *.c))
unopt64 = $(patsubst %.c,%.unopt64.exe,$(wildcard *.c))
opt32 = $(patsubst %.c,%.opt32.exe,$(wildcard *.c))
opt64 = $(patsubst %.c,%.opt64.exe,$(wildcard *.c))

all: $(unopt64) $(opt64)

%.unopt32.exe : %.c
	$(CC32) $(CFLAGS) -O0 $< -o $@

%.opt32.exe : %.c
	$(CC32) $(CFLAGS) -O2 $< -o $@

%.unopt64.exe : %.c
	$(CC64) $(CFLAGS) -O0 $< -o $@

%.opt64.exe : %.c
	$(CC64) $(CFLAGS) -O2 $< -o $@
