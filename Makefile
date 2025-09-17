COQMFFLAGS := -Q . SECF

#EXCLUDE := TestingFlexSLH.v TestingSpecCT.v # they don't yet work for Julay
ALLVFILES := $(filter-out $(EXCLUDE), $(wildcard *.v))

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf)

Makefile.coq: $(ALLVFILES)
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
