COQPROJECT_EXISTS=$(wildcard _CoqProject)

ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

NPAR=$(shell \
	hash gnproc &> /dev/null && \
		expr $$(gnproc) - 1 || \
		expr $$(nproc)  - 1 )

proof: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq

compcert:
	bash build_compcert.sh

compcert.ini: compcert/Makefile.config
	$(MAKE) -C compcert compcert.ini
	ln -sf compcert/compcert.ini compcert.ini

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
		OeufDriver.native

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm -rf Makefile.coq _build/
	rm -f extraction/*.ml extraction/*.mli

.PHONY: proof driver compcert clean
