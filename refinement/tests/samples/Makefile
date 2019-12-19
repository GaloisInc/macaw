# To build via nix:
# $ nix-shell -p pkgsCross.arm-embedded.buildPackages.gcc -p pkgsCross.ppc-embedded.buildPackages.gcc --run 'make CCPPC=powerpc64le-unknown-linux-musl-gcc CCARM=arm-none-eabi-gcc'
#
# n.b. do not use pkgsCross.musl-power: this is little-endian and
# results in: MissingTOCSection ".opd"

CCARM=arm-linux-gnu-gcc
CCPPC=powerpc64-linux-gnu-gcc
CCX86=clang

# armexe = $(patsubst %.c,%.arm.exe,$(wildcard *.c))
ppcexe = $(patsubst %.c,%.ppc.exe,$(wildcard *.c))
x86exe = $(patsubst %.c,%.x86.exe,$(wildcard *.c))

CFLAGS = -O0 -fno-stack-protector -g

all: $(ppcexe) $(x86exe)

$(armexe): %.arm.exe: %.arm.s
	$(CCARM) $(CFLAGS) -nostdlib $< -o $@

%.arm.s: %.c
	$(CCARM) $(CFLAGS) -S -c $< -o $@

$(ppcexe): %.ppc.exe: %.ppc.s
	$(CCPPC) $(CFLAGS) -nostdlib $< -o $@

%.ppc.s: %.c
	$(CCPPC) $(CFLAGS) -S -c $< -o $@

# NOTE: the PIE builds cannot be verified right now.  It looks like something in
# macaw is choking and not discovering the expected code for PIE binaries
$(x86exe): %.x86.exe: %.x86.s
	$(CCX86) $(CFLAGS) -no-pie -nostdlib $< -o $@

%.x86.s: %.c
	$(CCX86) $(CFLAGS) -no-pie -S -c $< -o $@

.PRECIOUS: %.s

clean:
	rm -f *.ppc.s *.ppc.exe *.x86.s *.x86.exe *.arm.s *.arm.exe
