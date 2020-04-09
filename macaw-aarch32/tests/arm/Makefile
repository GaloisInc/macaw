# n.b. nix packages for this arm gcc and related:
#    pkgsCross.arm-embedded.buildPackages.gcc

CCPROG != for X in arm-linux-gnueabi-gcc arm-none-eabi-gcc gcc ; do if type $$X > /dev/null 2>&1 ; then echo $$X; break; fi; done

A32CC := $(CCPROG)
T32CC := $(CCPROG) -mthumb

all: $(patsubst %.c,%-a32.exe,$(wildcard *.c)) $(patsubst %.c,%-t32.exe,$(wildcard *.c))

%-a32.exe: %-a32.s
	$(A32CC) -fno-stack-protector -nostdlib $< -o $@

%-t32.exe: %-t32.s
	$(T32CC) -fno-stack-protector -nostdlib $< -o $@

%-a32.s: %.c util.h
	$(A32CC) -fno-stack-protector -S -c $< -o $@

%-t32.s: %.c util.h
	$(T32CC) -fno-stack-protector -S -c $< -o $@

.PRECIOUS: %.s

clean:
	rm *.s *.exe

