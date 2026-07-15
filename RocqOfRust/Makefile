.PHONY: all clean clean-util distclean default watch generate plugin plugin-inline-print-check

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)
PLUGIN_INLINE_PRINT_TEST := plugin/test_inline_print.v
# The expected output is version-sensitive (scope-key printing and lemma
# re-exports changed after 9.2); select it alongside the compat shim below.
PLUGIN_INLINE_PRINT_EXPECTED := plugin/test_inline_print.expected
PLUGIN_INLINE_PRINT_OUTPUT := /tmp/rocqofrust-plugin-inline-print.out

PLUGIN_PACKAGES := \
	rocq-runtime.clib,rocq-runtime.config,rocq-runtime.engine,rocq-runtime.interp,rocq-runtime.kernel,rocq-runtime.lib,rocq-runtime.library,rocq-runtime.parsing,rocq-runtime.pretyping,rocq-runtime.printing,rocq-runtime.proofs,rocq-runtime.tactics,rocq-runtime.vernac
# Select the compat shim based on the Rocq version: the known-module
# registry was removed after 9.2.
ROCQ_LEGACY_MLTOP := $(shell coqc --version 2>/dev/null | grep -qE 'version (8\.|9\.[012]([^0-9]|$$))' && echo yes)
ifeq ($(ROCQ_LEGACY_MLTOP),yes)
PLUGIN_COMPAT_ML := plugin/compat/rocqofrust_plugin_compat_legacy.ml
else
PLUGIN_COMPAT_ML := plugin/compat/rocqofrust_plugin_compat_modern.ml
PLUGIN_INLINE_PRINT_EXPECTED := plugin/test_inline_print.dev.expected
endif

PLUGIN_ML := plugin/rocqofrust_plugin_compat.ml plugin/link_model.ml plugin/link_render.ml plugin/rocqofrust_link_plugin.ml

# Keep 'default' as the default goal: the rule below would otherwise
# become the first (and thus default) rule of the Makefile.
.DEFAULT_GOAL := default

# Always re-check (cheaply) so switching Rocq versions between builds
# picks the right shim; only copy on change to avoid rebuilds.
plugin/rocqofrust_plugin_compat.ml: $(PLUGIN_COMPAT_ML) FORCE
	@cmp -s $< $@ || cp $< $@

FORCE:

default: all

plugin: plugin/rocqofrust_link_plugin/rocqofrust_link_plugin.cmxs

plugin/rocqofrust_link_plugin/rocqofrust_link_plugin.cmxs: $(PLUGIN_ML) plugin/rocqofrust_link_plugin/META
	mkdir -p plugin/rocqofrust_link_plugin
	ocamlfind ocamlopt -I plugin -package $(PLUGIN_PACKAGES) -linkall -shared $(PLUGIN_ML) -o $@

plugin-inline-print-check: plugin $(PLUGIN_INLINE_PRINT_TEST) $(PLUGIN_INLINE_PRINT_EXPECTED)
	@echo "COQC plugin inline print $(PLUGIN_INLINE_PRINT_TEST)"
	@coqc -R . RocqOfRust -I plugin -impredicative-set $(PLUGIN_INLINE_PRINT_TEST) > $(PLUGIN_INLINE_PRINT_OUTPUT)
	@diff -u $(PLUGIN_INLINE_PRINT_EXPECTED) $(PLUGIN_INLINE_PRINT_OUTPUT)

# We use the '@' to avoid displaying this command as the parameters list is
# very long.
RocqMakefile: plugin $(VFILES) blacklist.txt
	@coq_makefile -f _RocqProject -o $@ $(VFILES)

MAKEROCQ := +$(MAKE) -f RocqMakefile

%.vo: plugin RocqMakefile %.v
	$(MAKEROCQ) $@

all: plugin RocqMakefile
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
