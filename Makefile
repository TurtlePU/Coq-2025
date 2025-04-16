COQMFFLAGS := -Q . Lectures

ALLVFILES := Lecture1.v Lecture1Test.v Lecture2.v Lecture2Test.v Lecture3.v Lecture3Test.v Lecture4.v Lecture4Test.v Lecture5.v Lecture5Test.v Lecture6.v Lecture6Test.v
build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf) imp.ml imp.mli imp1.ml imp1.mli imp2.ml imp2.mli

Makefile.coq:
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
