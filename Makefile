COQMFFLAGS := -Q . SECF

EXCLUDE := LinearProof.v TestingFlexSLH.v TestingSpecCT.v TestingStaticIFC.v #  TestingMiniCETSync.v Machine.v MachineProof.v # they don't yet work for Julay
ALLVFILES := $(filter-out $(EXCLUDE), $(wildcard *.v))
QC := quickChick # ../QuickChick/quickChickTool/quickChickTool.exe
QCFLAGS := -color -top SECF -N 100 -failfast -cmd "make -j >/dev/null 2>&1 && echo 'compilation done'" # -ntests 100,1000,10000

build: Makefile.coq
	$(MAKE) -f Makefile.coq

clean::
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) $(wildcard Makefile.coq Makefile.coq.conf)
	rm -rf ../_qc_$(shell basename $(CURDIR)).tmp *.bak

test: Makefile.coq clean
	@if [ -z "$(EXCLUDE)" ]; then \
		$(QC) $(QCFLAGS); \
	else \
		$(QC) $(QCFLAGS) -exclude $(EXCLUDE); \
	fi

Makefile.coq: $(ALLVFILES)
	coq_makefile $(COQMFFLAGS) -o Makefile.coq $(ALLVFILES)

-include Makefile.coq

.PHONY: build clean
