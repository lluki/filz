all: Main Test

debug: i2c.c
	cat i2c.c

Main: *.hs
	ghc Main.hs

Test: *.hs
	ghc Test.hs

run_test: Test
	./Test
	

%.xpp: %.xp
	gcc -xc -undef -E $< | grep -v ^\# > $@

%.pml: %.xpp Main %.xpp
	./Main -P all $< $@

%.c: %.xpp Main %.xpp
	./Main -C all $< $@
	clang-format -i $@

clean:
	rm -f Test Main *.hi *.o *.pml *.xpp
