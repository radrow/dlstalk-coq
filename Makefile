.PHONY: all
all: proofs

.PHONY: proofs
proofs: Makefile.coq
	@printf "`tput bold`*** PROOFS START ***`tput sgr0`\n" || echo "*** PROOFS START ***"
	@+$(MAKE) -f Makefile.coq all
	@printf "`tput bold; tput setaf 2`*** `tput blink`SUCCESS`tput sgr0;tput bold;tput setaf 2` ***`tput sgr0`\n" || echo "*** SUCCESS ***"

.PHONY: clean
clean: Makefile.coq
	@+$(MAKE) -f Makefile.coq cleanall
	@rm -f Makefile.coq Makefile.coq.conf

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

.PHONY: force
force _CoqProject Makefile: ;

%: Makefile.coq force
	@+$(MAKE) -f Makefile.coq $@

