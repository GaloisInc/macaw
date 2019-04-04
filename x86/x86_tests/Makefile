tests = btx_test.exe ucomis_test.exe pop_test.exe ret_test.exe

run : $(tests)
	set -e; for v in $(tests); do echo "Running $$v"; ./$$v; done

%_test.exe : %_test.c %_run.s utils.h
	clang -o $@ $*_test.c $*_run.s

test_%.exe : test_%.c %.s utils.h
	clang -o $@ test_$*.c $*.s

clean :
	rm -rf $(tests)

.PHONY : run clean
