CC=powerpc-linux-gnu-gcc-8
all: $(patsubst %c,%exe,$(wildcard *.c))

%.exe: %.s
	$(CC) -fno-stack-protector -nostdlib $< -o $@

%.s: %.c
	$(CC) -fno-stack-protector -S -c $< -o $@

# This test relies on the binary having dynamic relocations.
test-relocs.exe: test-relocs.s
	$(CC) -fno-stack-protector -nostartfiles $< -o $@

.PRECIOUS: %.s

clean:
	rm *.s *.exe

