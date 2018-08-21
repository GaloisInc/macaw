A32CC=arm-linux-gnueabi-gcc
# arm-none-eabi-gcc
T32CC=arm-linux-gnueabi-gcc -mthumb
# -march=armv7-m
# arm-none-eabi-gcc -march=armv7-m

all: $(patsubst %.c,%-a32.exe,$(wildcard *.c)) $(patsubst %.c,%-t32.exe,$(wildcard *.c))

%-a32.exe: %-a32.s
	$(A32CC) -fno-stack-protector -nostdlib $< -o $@

%-t32.exe: %-t32.s
	$(T32CC) -fno-stack-protector -nostdlib $< -o $@

%-a32.s: %.c
	$(A32CC) -fno-stack-protector -S -c $< -o $@

%-t32.s: %.c
	$(T32CC) -fno-stack-protector -S -c $< -o $@

.PRECIOUS: %.s

clean:
	rm *.s *.exe

