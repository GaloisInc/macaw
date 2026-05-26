exe_testcases := $(patsubst %exe.expected,%exe, $(wildcard *.exe.expected))
obj_testcases := $(patsubst %o.expected,%o, $(wildcard *.o.expected))

all: $(exe_testcases) $(obj_testcases)

# We have a special rule for the tail call test case because we need
# -O2 to convince gcc to emit a tail call, but we'd rather not have
# that much aggressive optimization for the other tests because it
# usually makes them trivial.
test-tail-call.exe: test-tail-call.c
	gcc -fno-stack-protector -O2 -fno-inline -S -c $< -o test-tail-call.s
	gcc -fno-stack-protector -O2 -fno-inline -nostdlib $< -o $@

# Jump table bounded by bitmask needs -O2 to emit the table and -fno-pic
# to avoid PC-relative relocations that macaw can't handle in object files.
test-jumptable-mask.o: test-jumptable-mask.c
	clang -c --target=x86_64-pc-linux-elf -O2 -fno-pic -o $@ $<

# Regression test for mergeIntraJump not joining jump bounds.
# Needs -O1 to keep the explicit comparisons and -fno-jump-tables to keep
# the chained conditional branches instead of emitting a jump table.
test-mergeintrajump.o: test-mergeintrajump.c
	clang -c --target=x86_64-pc-linux-elf -O1 -fno-jump-tables -o $@ $<

%.exe: %.s
	gcc -fno-stack-protector -nostdlib $< -o $@

%.s: %.c
	gcc -fno-stack-protector -foptimize-sibling-calls -S -c $< -o $@

%.o: %.c
	clang -c --target=x86_64-pc-linux-elf -o $@ $<

%.o: %.s
	clang -c --target=x86_64-pc-linux-elf -o $@ $<

.PRECIOUS: %.s

clean:
	rm -f *.o *.s *.exe
