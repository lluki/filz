SHELL:=/bin/bash
GCCOPTS=-Wall -Wno-unused-value -Wno-unused-label -Os
# Append so we can set options in env
SPINOPTS+=-E-I$(shell pwd)/build -E-I$(shell pwd)/xp-src -E-I$(shell pwd)/spin-src
# Conditional assign so we can set it in env
SEARCH_DEPTH?=1000000

all: build/as5011.pml build/eep.pml build/eep.c build/test-symbol-reader example verif

# the common PML files
PML=build/as5011.pml build/eep.pml build/example.pml spin-src/i2c-spec.pml xp-src/common.xp

#.PHONY: paper
#paper: paper/paper.pdf
#paper/paper.pdf: paper/*.tex
#	cd paper && make

## Basename for runspin and runreplay
BASENAME=as5011-eq
ABS_LEVEL=0

.PHONY: runspin
runspin: $(PML) spin-src/$(BASENAME).pml
	@echo "ABS_LEVEL=$(ABS_LEVEL)"
	cd build && spin -DABS_LEVEL=$(ABS_LEVEL) -u$(SEARCH_DEPTH) $(SPINOPTS) ../spin-src/$(BASENAME).pml 

.PHONY: runpspin
runpspin: $(PML) spin-src/$(BASENAME).pml
	@echo "ABS_LEVEL=$(ABS_LEVEL)"
	cd build && spin -DABS_LEVEL=$(ABS_LEVEL) -s -p -u$(SEARCH_DEPTH) $(SPINOPTS) ../spin-src/$(BASENAME).pml 

.PHONY: runreplay
runreplay: 
	# spin really wants all the files in the same directory, hence
	# copy everything to the build dir
	cp $(BASENAME).pml.trail build/
	cp xp-src/common.xp build/
	cp spin-src/$(BASENAME).pml build/
	cp spin-src/i2c-spec.pml build/
	cd build && spin -p -replay -u10000 $(BASENAME).pml 

.PHONY: verif-echo
verif-echo: build/verif/el-master-echo \
			build/verif/sym-eq \
			build/verif/byte-echo

.PHONY: verif
verif: build/verif/sym-eq \
	   build/verif/byte-eq \
	   build/verif/transaction-eq \
	   build/verif/hl-eq

as5011-verif: build/verif/as5011-eq

.PHONY: quickverif
quickverif: build/verif/sym-eq
#PANCCOPTS+=-DVECTORSZ=4096 -Wno-format-overflow #-O3 #-DNCORE=8 
PANCCOPTS+=-DVECTORSZ=4096 -Wno-format-overflow #-DNP #-O3 #-DNCORE=8 


build/verif/byte-eq/full.txt: spin-src/byte-eq.pml  $(PML) 
	echo "Verifying byte-eq FULL"
	mkdir -p build/verif/byte-eq
	cd build/verif/byte-eq; \
		spin -a -DABS_LEVEL=1 -DBYTE_FULL $(SPINOPTS) ../../../spin-src/byte-eq.pml 2> /dev/null ; \
		cc $(PANCCOPTS) -DNCORE=24 -O3 -o pan pan.c ; \
		./pan -m$(SEARCH_DEPTH) -n > full.txt 
	
		

build/verif/%: spin-src/%.pml  $(PML) 
	# We build two pan's here, one for the non-progress cycle detection pan_np
	# and one for the invalid end state. they seem to be incompatible.
	echo "Verifying $@   $<"
	@mkdir -p $@
	@cd $@; for x in {0..4}; do \
		echo "  Using ABS_LEVEL=$$x"; \
		if ! spin -a -DABS_LEVEL=$$x $(SPINOPTS) ../../../$< 2> /dev/null ; then \
			echo "skip" ; \
			continue ; \
		fi ; \
		cc $(PANCCOPTS) -o pan pan.c ;\
		cc $(PANCCOPTS) -DNP -o pan_np pan.c ;\
		./pan -m$(SEARCH_DEPTH) -n > $$x.txt ;\
		./pan_np -l -m$(SEARCH_DEPTH) -n > $$x-np.txt ;\
		echo "  Result in $@/$$x.txt" ;\
		grep "errors" $$x.txt ;\
		grep "errors" $$x-np.txt ;\
		! grep 'max search depth too small' $$x.txt ;\
		! grep 'max search depth too small' $$x-np.txt ;\
		! grep 'assertion violated' $$x.txt ;\
		! grep 'assertion violated' $$x-np.txt ;\
	done

#build/verif-example-eq: $(PML) spin-src/example-eq.pml
#	cd build && spin -a $(SPINOPTS) ../spin-src/example-eq.pml
#	cc $(PANCCOPTS) -o build/pan build/pan.c
#	cd build && ./pan -m$(SEARCH_DEPTH) -n > verif-example-eq
#	@echo "Verification of example-eq written to build/verif-example-eq"
#	@grep "errors" build/verif-example-eq
#	@! grep 'max search depth too small' build/verif-example-eq
#	@! grep 'assertion violated' build/verif-example-eq

#build/verif-hl-eq: $(PML) spin-src/hl-eq.pml
#	cd build && spin -a $(SPINOPTS) ../spin-src/hl-eq.pml
#	cc $(PANCCOPTS) -o build/pan build/pan.c
#	cd build && ./pan -m$(SEARCH_DEPTH) -n  > verif-hl-eq
#	@echo "Verification of hl-eq written to build/verif-hl-eq"
#	@grep "errors" build/verif-hl-eq
#	@! grep 'max search depth too small' build/verif-hl-eq
#	@! grep 'assertion violated' build/verif-hl-eq
#
#build/verif-transaction-eq: $(PML) spin-src/transaction-eq.pml
#	cd build && spin -a $(SPINOPTS) ../spin-src/transaction-eq.pml
#	cc $(PANCCOPTS) -o build/pan build/pan.c
#	cd build && ./pan -m$(SEARCH_DEPTH) -n  > verif-transaction-eq
#	@echo "Verification of transaction-eq written to build/verif-transaction-eq"
#	@grep "errors" build/verif-transaction-eq
#	@! grep 'max search depth too small' build/verif-transaction-eq
#	@! grep 'assertion violated' build/verif-transaction-eq
#
#build/verif-byte-eq: $(PML) spin-src/byte-eq.pml
#	cd build && spin -a $(SPINOPTS) ../spin-src/byte-eq.pml
#	cc $(PANCCOPTS) -o build/pan build/pan.c
#	cd build && ./pan -m$(SEARCH_DEPTH) -n  > verif-byte-eq
#	@echo "Verification of byte-eq written to build/verif-byte-eq"
#	@grep "errors" build/verif-byte-eq
#	@! grep 'max search depth too small' build/verif-byte-eq
#	@! grep 'assertion violated' build/verif-byte-eq
#
#build/verif-byte-echo: $(PML) spin-src/byte-echo.pml
#	cd build && spin -a $(SPINOPTS) ../spin-src/byte-echo.pml
#	cc $(PANCCOPTS) -o build/pan build/pan.c
#	cd build && ./pan -m$(SEARCH_DEPTH) -n  > verif-byte-echo
#	@echo "Verification of byte-echo written to build/verif-byte-echo"
#	@grep "errors" build/verif-byte-echo
#	@! grep 'max search depth too small' build/verif-byte-echo
#	@! grep 'assertion violated' build/verif-byte-echo
#
#build/verif-el-eq-sym: $(PML) spin-src/el-eq-sym.pml
#	cd build && spin -a $(SPINOPTS) ../spin-src/el-eq-sym.pml
#	cc $(PANCCOPTS) -o build/pan build/pan.c
#	cd build && ./pan -m$(SEARCH_DEPTH) -n  > verif-el-eq-sym
#	@echo "Verification of el-eq-sym written to build/verif-el-eq-sym"
#	@grep "errors" build/verif-el-eq-sym
#	@! grep 'max search depth too small' build/verif-el-eq-sym
#	@! grep 'assertion violated' build/verif-el-eq-sym
#
#build/verif-el-master-echo: $(PML) spin-src/el-master-echo.pml
#	cd build && spin -a $(SPINOPTS) ../spin-src/el-master-echo.pml
#	cc $(PANCCOPTS) -o build/pan build/pan.c
#	(cd build && ./pan -n  > verif-el-master-echo)
#	@echo "Verification of el-master-echo written to build/verif-el-master-echo"
#	@grep "errors" build/verif-el-master-echo
#	@! grep 'max search depth too small' build/verif-el-master-echo
#	@! grep 'assertion violated' build/verif-el-master-echo


## Verification Benchmarks & Plots
.PHONY: verif-time-table
verif-time-table: tools/build-table.py
	@echo "!! Assuming your benchmarks have run !!"
	@mkdir -p paper/includes
	@./tools/build-table.py | tee paper/includes/verif-table.tex
	

.PHONY: verif-time-results
verif-time-results: benchmarks/verification_time.sh
	mkdir -p verif-time-results
	cd verif-time-results && ../benchmarks/verification_time.sh

.PHONY: verif-time-plots
verif-time-plots: benchmarks/verification_time_plots.py
	mkdir -p verif-time-plots
	benchmarks/verification_time_plots.py -r verif-time-results -o verif-time-plots

## Targets for the example
.PHONY: example
example: build/example.pml build/verif/example-eq
	

.PHONY: run run_spin_gen_test
run: build/test-symbol-reader
	./build/test-symbol-reader

run_spin_gen_test: spin-gen/Test
	cd spin-gen && ./Test


spin-gen/Main spin-gen/Test: spin-gen/*.hs
	cd spin-gen && make

build/test-symbol-reader: build/test-symbol-reader.c build/i2c-test-symbol-reader.c build/i2c-test-symbol-reader.h
	cd build && gcc $(GCCOPTS) i2c-test-symbol-reader.c test-symbol-reader.c -o test-symbol-reader

build/test-symbol-reader.c: xp-src/test-symbol-reader.c
	cp xp-src/test-symbol-reader.c build/test-symbol-reader.c

GEN_MACHINES=controller_Sym

build/i2c-test-symbol-reader.c: spin-gen/Main build/eep.xpp
	mkdir -p build
	./spin-gen/Main -i build/eep.xpp -m$(GEN_MACHINES) -C -o $@
	clang-format -i $@

build/i2c-test-symbol-reader.h: spin-gen/Main build/eep.xpp
	mkdir -p build
	./spin-gen/Main -i build/eep.xpp -H -o $@

build/test.h: spin-gen/Main build/test.xpp
	mkdir -p build
	./spin-gen/Main -i build/eep.xpp -H -o $@

build/rpi: build/eep.c build/eep.h spin-src/rpi-boilerplate.c
	mkdir -p build
	cp spin-src/rpi-boilerplate.c build/rpi-boilerplate.c
	cd build && gcc $(GCCOPTS) eep.c rpi-boilerplate.c -o rpi


build/%.xpp: xp-src/%.xp
	mkdir -p build
	gcc -xc -undef -E $< | grep -v ^\# > $@

build/%.pml: build/%.xpp spin-gen/Main build/%.xpp
	mkdir -p build
	./spin-gen/Main -i $< -P -o $@

build/%.c: build/%.xpp spin-gen/Main build/%.xpp
	mkdir -p build
	./spin-gen/Main -i $< -C -o $@
	clang-format -i $@

build/%.h: build/%.xpp spin-gen/Main build/%.xpp
	mkdir -p build
	./spin-gen/Main -i $< -H -o $@

.PHONY: count
count: build/eep.c build/rpi
	echo "RPI boilerplate LOC:"
	wc -l spin-src/rpi-boilerplate.c 
	echo "I2C state machines LOC:"
	wc -l build/i2c.c 
	echo "RPI test tool size (local architecture)"
	ls -sh build/rpi

clean:
	cd spin-gen && make clean
	cd paper && make clean
	rm -rf build


.PHONY: release
release: clean 
	echo "Creating release in ../filz"
	mkdir -p ../filz
	cp -R spin-src ../filz
	cp -R spin-gen ../filz
	cp -R xp-src ../filz
	cp -R docs ../filz
	cp Makefile ../filz/Makefile
	cp README.md ../filz/README.md
