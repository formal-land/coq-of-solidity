.PHONY: all clean clean-util distclean default

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)

default: all

RocqMakefile: $(VFILES) blacklist.txt
	echo "-R . RocqOfSolidity" > _RocqProject
	echo "-arg -impredicative-set -arg -w -arg -stdlib-vector" >> _RocqProject
	# We copy & paste the command to find files as this variable is too long on command line
	find -L . -name "*.v" | grep -v -f blacklist.txt | sort >> _RocqProject
	coq_makefile -f _RocqProject -o $@

MAKEROCQ := +$(MAKE) -f RocqMakefile

%.vo: RocqMakefile %.v
	$(MAKEROCQ) $@

all: RocqMakefile
	$(MAKEROCQ) all

clean-rocq: RocqMakefile
	$(MAKEROCQ) clean

clean-util:
	rm -f *RocqMakefile*

clean: clean-rocq
	$(MAKE) clean-util # done separately to enforce order

distclean: clean
