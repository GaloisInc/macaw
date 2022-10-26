CC=arm-linux-gnueabi-gcc
CFLAGS=-nostdlib -static -fno-stack-protector

unopt = $(patsubst %.c,%.unopt.exe,$(wildcard *.c))
opt = $(patsubst %.c,%.opt.exe,$(wildcard *.c))

all: $(unopt) $(opt)

%.unopt.exe : %.c
	$(CC) $(CFLAGS) -O0 $< -o $@

%.opt.exe : %.c
	$(CC) $(CFLAGS) -O2 $< -o $@

# We have to use -O1 for this case; -O0 won't generate a conditional return,
# while -O2 generates some totally different code where the compiler just
# conditionally performs a bunch of other operations instead
test-conditional-return.opt.exe: test-conditional-return.c
	$(CC) $(CFLAGS) -O1 $< -o $@

# We need to pass -mcpu=cortex-a7 here
movt.unopt.exe: movt.c
	$(CC) $(CFLAGS) -mcpu=cortex-a7 -O0 $< -o $@
movt.opt.exe: movt.c
	$(CC) $(CFLAGS) -mcpu=cortex-a7 -O2 $< -o $@
