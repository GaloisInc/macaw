CC=powerpc64-linux-gnu-gcc
all: $(patsubst %c,%exe,$(wildcard *.c))

%.exe: %.s
	$(CC) -fno-stack-protector -nostdlib $< -o $@

%.s: %.c
	$(CC) -fno-stack-protector -S -c $< -o $@

.PRECIOUS: %.s

clean:
	rm *.s *.exe

