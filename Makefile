NPAR=$(shell \
	hash gnproc > /dev/null 2>&1 && \
		expr $$(gnproc) - 1 || \
		expr $$(nproc)  - 1 )

COMPCERTCONFIG=$(shell \
	[ "$$(uname)" = "Darwin" ] && \
		echo "ia32-macosx" || \
		echo "ia32-linux"  )

DRIVER=OeufDriver.native

all: compcert proof driver plugin

compcert:
	cd compcert && ./configure $(COMPCERTCONFIG)
	$(MAKE) -j $(NPAR) -C compcert proof
	$(MAKE) -j $(NPAR) -C compcert driver/Version.ml
	$(MAKE) -j $(NPAR) -C compcert -f Makefile.extr \
		cparser/pre_parser_messages.ml

proof: Makefile.coq
	$(MAKE) -j $(NPAR) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

_CoqProject:
	./configure

plugin:
	make -C plugin

driver: compcert.ini
	ocamlbuild \
		-use-menhir -pkg menhirLib \
		-yaccflag --table \
		-j $(NPAR) \
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

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf Makefile.coq _build/
	rm -f compcert.ini $(DRIVER)
	rm -f extraction/*.ml extraction/*.mli

cleaner: clean
	$(MAKE) -C compcert clean

.PHONY: all compcert proof driver clean cleaner plugin
