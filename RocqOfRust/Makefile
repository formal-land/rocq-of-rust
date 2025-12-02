.PHONY: all clean clean-util distclean default watch generate

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)

default: all

# We use the '@' to avoid displaying this command as the parameters list is
# very long.
RocqMakefile: $(VFILES) blacklist.txt
	@coq_makefile -f _RocqProject -o $@ $(VFILES)

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

watch:
	while true; do \
		inotifywait -e modify $(VFILES) Makefile; \
		make -k -j3; \
	done

GENERATE_FILES := $(shell find . -type f -name "generate.py")

generate: $(GENERATE_FILES)
	@for file in $(GENERATE_FILES); do \
		echo "python $$file"; \
		python $$file; \
	done