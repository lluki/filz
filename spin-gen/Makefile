all: Main

debug: i2c.c
	cat i2c.c

Main: Main.hs *.hs
	ghc Main.hs

%.xpp: %.xp
	gcc -xc -undef -E $< | grep -v ^\# > $@

%.pml: %.xpp Main %.xpp
	./Main -P all $< $@

%.c: %.xpp Main %.xpp
	./Main -C all $< $@
	clang-format -i $@

clean:
	rm -f Main *.hi *.o *.pml *.xpp
