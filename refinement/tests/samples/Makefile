# To build via nix:
# $ nix-shell -p pkgsCross.arm-embedded.buildPackages.gcc -p pkgsCross.ppc-embedded.buildPackages.gcc --run 'make CCPPC=powerpc64le-unknown-linux-musl-gcc CCARM=arm-none-eabi-gcc'
#
# n.b. do not use pkgsCross.musl-power: this is little-endian and
# results in: MissingTOCSection ".opd"

# CCARM=arm-linux-gnu-gcc
GCCPPC=powerpc64-linux-gnu-gcc
GCCX86=gcc
CLANGX86=clang

CFLAGS = -O0 -fno-stack-protector -g
CFLAGS_OPT = -O1 -fno-stack-protector -g

OPT = noopt opt
PIE = pie nopie
ppc_targets = $(foreach opt,$(OPT),$(foreach pie,$(PIE),$(patsubst %.c,%.ppc.gcc.$(pie).$(opt).exe,$(wildcard *.c))))
COMPILER = clang gcc
x86_targets = $(foreach compiler,$(COMPILER),$(foreach opt,$(OPT),$(foreach pie,$(PIE),$(patsubst %.c,%.x86.$(compiler).$(pie).$(opt).exe,$(wildcard *.c)))))

all: $(ppc_targets) $(x86_targets)

# PowerPC
%.ppc.gcc.nopie.noopt.exe: %.c
	$(GCCPPC) $(CFLAGS) -nostdlib -no-pie $< -o $@

%.ppc.gcc.nopie.opt.exe: %.c
	$(GCCPPC) $(CFLAGS_OPT) -nostdlib -no-pie $< -o $@

%.ppc.gcc.pie.noopt.exe: %.c
	$(GCCPPC) $(CFLAGS) -nostdlib -pie $< -o $@

%.ppc.gcc.pie.opt.exe: %.c
	$(GCCPPC) $(CFLAGS_OPT) -nostdlib -pie $< -o $@

# X86/gcc
%.x86.gcc.nopie.noopt.exe: %.c
	$(GCCX86) $(CFLAGS) -nostdlib -no-pie $< -o $@

%.x86.gcc.nopie.opt.exe: %.c
	$(GCCX86) $(CFLAGS_OPT) -nostdlib -no-pie $< -o $@

%.x86.gcc.pie.noopt.exe: %.c
	$(GCCX86) $(CFLAGS) -nostdlib -pie $< -o $@

%.x86.gcc.pie.opt.exe: %.c
	$(GCCX86) $(CFLAGS_OPT) -nostdlib -pie $< -o $@

# X86/clang
%.x86.clang.nopie.noopt.exe: %.c
	$(CLANGX86) $(CFLAGS) -nostdlib -no-pie $< -o $@

%.x86.clang.nopie.opt.exe: %.c
	$(CLANGX86) $(CFLAGS_OPT) -nostdlib -no-pie $< -o $@

%.x86.clang.pie.noopt.exe: %.c
	$(CLANGX86) $(CFLAGS) -nostdlib -pie -fPIE $< -o $@

%.x86.clang.pie.opt.exe: %.c
	$(CLANGX86) $(CFLAGS_OPT) -nostdlib -pie -fPIE $< -o $@


clean:
	rm -f *.exe
