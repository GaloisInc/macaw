tests = btx_test.exe ucomis_test.exe pop_test.exe ret_test.exe

run : $(tests)
	set -e; for v in $(tests); do echo "Running $$v"; ./$$v; done

%.o : %.s
	clang -c -o $@ $<

%.o : %.c
	clang -c -Wall -Werror -std=c11 -o $@ $<

expect_segfault.o : utils.h expect_segfault.h

%_test.exe : %_test.o %_run.o utils.h
	clang -o $@ $(filter %.o,$^)
# ($^:%.o=%.o)

fsgs_test.exe : expect_segfault.o

clean :
	rm -rf $(tests)

.PHONY : run clean
.PRECIOUS : %.o
