run : test_btx test_ucomis test_ret
	./test_btx
	./test_ucomis
	./test_ret

test_btx : test_btx.c btx.s utils.h
	clang -o test_btx test_btx.c btx.s

test_ucomis : test_ucomis.c ucomis.s utils.h
	clang -o test_ucomis test_ucomis.c ucomis.s

test_ret : test_ret.c ret.s utils.h
	clang -o test_ret test_ret.c ret.s

clean :
	rm -rf test_btx test_ucomis test_ret

.PHONY : run clean
