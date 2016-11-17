.PHONY: all clean 
COQMAKEFILE := Makefile.coq
ifneq "$(COQBIN)" ""
  COQBIN := $(COQBIN)/
endif

all: $(COQMAKEFILE)
		+$(MAKE) -f $(COQMAKEFILE) $@

clean:
	-$(MAKE) -f $(COQMAKEFILE) clean
	rm -f $(COQMAKEFILE)

$(COQMAKEFILE): Makefile 
	$(COQBIN)coq_makefile -f Make -o Makefile.coq

%.vo:: $(COQMAKEFILE)
	make -f $(COQMAKEFILE) -j$(CORES) $@

