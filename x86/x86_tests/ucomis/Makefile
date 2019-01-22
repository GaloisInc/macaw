run : test_ucomis
	./test_ucomis

test_ucomis : test_ucomis.c
	clang -o test_ucomis test_ucomis.c ucomis.s

clean :
	rm -rf test_ucomis

.PHONY : run clean
