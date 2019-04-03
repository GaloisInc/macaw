run : test_btx test_ucomis
	./test_btx
	./test_ucomis

test_btx : test_btx.c btx.s utils.h
	clang -o test_btx test_btx.c btx.s

test_ucomis : test_ucomis.c
	clang -o test_ucomis test_ucomis.c ucomis.s

clean :
	rm -rf test_btx test_ucomis

.PHONY : run clean
