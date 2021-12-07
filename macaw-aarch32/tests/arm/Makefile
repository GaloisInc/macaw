# n.b. nix packages for this arm gcc and related:
#    pkgsCross.arm-embedded.buildPackages.gcc

CCPROG != for X in arm-linux-gnueabi-gcc arm-none-eabi-gcc gcc ; do if type $$X > /dev/null 2>&1 ; then echo $$X; break; fi; done

A32AS := arm-linux-gnueabi-as
A32LD := arm-linux-gnueabi-ld
A32CC := $(CCPROG)
T32CC := $(CCPROG) -mthumb

all: $(patsubst %.c,%-a32.exe,$(wildcard *.c)) $(patsubst %.c,%-t32.exe,$(wildcard *.c)) syscall-a32.exe

%-a32.exe: %-a32.s
	$(A32CC) -fno-stack-protector -nostdlib $< -o $@

%-t32.exe: %-t32.s
	$(T32CC) -fno-stack-protector -nostdlib $< -o $@

%-mixed.exe: %-mixed.s
	$(A32CC) -fno-stack-protector -nostdlib $< -o $@

%-a32.s: %.c util.h
	$(A32CC) -fno-stack-protector -S -c $< -o $@

%-t32.s: %.c util.h
	$(T32CC) -fno-stack-protector -S -c $< -o $@

%-mixed.s: %-mixed.c
	$(A32CC) -fno-stack-protector -S -c $< -o $@

syscall.o: syscall.s
	$(A32AS) $< -o $@

syscall-a32.exe: syscall.o
	$(A32LD) $< -o $@

.PRECIOUS: %.s

clean:
	rm *.s *.exe

