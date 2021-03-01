CC=gcc
CFLAGS=-nostdlib -static -fno-stack-protector

unopt = $(patsubst %.c,%.unopt.exe,$(wildcard *.c))
opt = $(patsubst %.c,%.opt.exe,$(wildcard *.c))

all: $(unopt) $(opt)

%.unopt.exe : %.c
	$(CC) $(CFLAGS) -O0 $< -o $@

%.opt.exe : %.c
	$(CC) $(CFLAGS) -O2 $< -o $@
