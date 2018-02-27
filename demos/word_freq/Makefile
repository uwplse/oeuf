COQPROJECT_EXISTS=$(wildcard _CoqProject)

ifeq "$(COQPROJECT_EXISTS)" ""
$(error "Run ./configure before running make")
endif

shim_proofs: word_freq Makefile.shim_proofs
	$(MAKE) -f Makefile.shim_proofs

word_freq: word_freq.oeuf src/shim.c
	~/oeuf/OeufDriver.native word_freq.oeuf src/shim.c -o word_freq -I ~/oeuf/ -stdlib ~/oeuf/compcert/runtime/
	mv word_freq_oeuf.v src/
	mv word_freq_cm.v src/

word_freq.oeuf: Makefile.coq src/Freq.v
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject.prelim
	coq_makefile -f _CoqProject.prelim -o Makefile.coq

Makefile.shim_proofs: _CoqProject.shim_proofs
	coq_makefile -f _CoqProject.shim_proofs -o Makefile.shim_proofs

clean:
	$(MAKE) -f Makefile.coq clean
	rm -f Makefile.coq
	rm -f Makefile.shim_proofs
	rm -f word_freq word_freq.o
	rm -f word_freq_cm.v word_freq_oeuf.v

.PHONY: default clean
