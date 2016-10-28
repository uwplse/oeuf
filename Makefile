DRIVER=OeufDriver.native

all: proof driver test

proof: Makefile.coq
ifeq ($(NPAR),)
	$(MAKE) -j2 -f Makefile.coq
else
	$(MAKE) -j$(NPAR) -f Makefile.coq
endif

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

plugin:
	make -C plugin

sanitize:
	_build/sanitize.sh || true

driver: compcert.ini sanitize
	ocamlbuild \
		-use-menhir -pkg menhirLib \
		-yaccflag --table \
		-lib str \
		-lib unix \
		-I src \
		-I extraction \
		-I compcert/driver \
		-I compcert/cfrontend \
		-I compcert/cparser \
		-I compcert/ia32 \
		-I compcert/lib \
		-I compcert/common \
		-I compcert/debug \
		-I compcert/backend \
		$(DRIVER)
	rm -f $(DRIVER)
	cp _build/src/$(DRIVER) $(DRIVER)

compcert.ini: compcert/Makefile.config
	$(MAKE) -C compcert compcert.ini
	rm -f compcert.ini
	cp compcert/compcert.ini compcert.ini

test:
	./test.sh

demo :
	./compile_demo.sh

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf Makefile.coq _build/
	rm -f compcert.ini $(DRIVER)
	rm -f extraction/*.ml extraction/*.mli

COMPCERTCONFIG=$(shell \
	[ "$$(uname)" = "Darwin" ] && \
		echo "ia32-macosx" || \
		echo "ia32-linux"  )

COMPCERTPAR=$(shell \
	[ "$$(hostname -s)" = "warfa" ] && \
		echo "-j6" || \
		echo ""  )

compcert:
	cd compcert && ./configure $(COMPCERTCONFIG)
	$(MAKE) $(COMPCERTPAR) -C compcert

cleaner: clean
	$(MAKE) -C compcert clean

.PHONY: all proof driver plugin sanitize test clean compcert cleaner
