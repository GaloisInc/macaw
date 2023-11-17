CC=arm-linux-gnueabi-gcc
CFLAGS=-nostdlib -static -fno-stack-protector
SO_CFLAGS=-nostdlib -fno-stack-protector -fcf-protection=none

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

# We need to pass -mcpu=cortex-a7 here
strd.unopt.exe: strd.s
	$(CC) $(CFLAGS) -mcpu=cortex-a7 -O0 $< -o $@
strd.opt.exe: strd.s
	$(CC) $(CFLAGS) -mcpu=cortex-a7 -O2 $< -o $@

so/libfib.unopt.so: so/fib.c so/libgetone.unopt.so
	$(CC) $(SO_CFLAGS) -O0 -Lso/ -Iso/ -shared $< -lgetone.unopt -o $@
so/libfib.opt.so: so/fib.c so/libgetone.opt.so
	$(CC) $(SO_CFLAGS) -O2 -Lso/ -Iso/ -shared $< -lgetone.opt -o $@

so/libgetone.unopt.so : so/getone.c
	$(CC) $(SO_CFLAGS) -O0 -Iso/ -shared $< -o $@
so/libgetone.opt.so : so/getone.c
	$(CC) $(SO_CFLAGS) -O2 -Iso/ -shared $< -o $@

so/so.unopt.exe : so/so.c so/libfib.unopt.so
	$(CC) $(SO_CFLAGS) -O0 -Lso/ -Iso/ $< -lfib.unopt -lgetone.unopt -o $@
so/so.opt.exe : so/so.c so/libfib.opt.so
	$(CC) $(SO_CFLAGS) -O2 -Lso/ -Iso/ $< -lfib.opt -lgetone.opt -o $@
