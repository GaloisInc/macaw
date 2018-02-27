A32CC=arm-none-eabi-gcc
T32CC=arm-none-eabi-gcc -march=armv7-m

all: $(patsubst %.c,%-a32.exe,$(wildcard *.c)) $(patsubst %.c,%-t32.exe,$(wildcard *.c))

%-a32.exe: %.s
	$(A32CC) -fno-stack-protector -nostdlib $< -o $@

%-t32.exe: %.s
	$(T32CC) -fno-stack-protector -nostdlib $< -o $@

%-a32.s: %.c
	$(CC) -fno-stack-protector -S -c $< -o $@

%-t32.s: %.c
	$(CC) -march=thumb -fno-stack-protector -S -c $< -o $@

.PRECIOUS: %.s

clean:
	rm *.s *.exe

