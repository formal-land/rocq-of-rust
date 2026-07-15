.PHONY: all clean clean-util distclean default watch generate plugin plugin-inline-print-check \
	evaluate-translated-examples evaluate-translated-add-one \
	evaluate-translated-choose-and-add

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)
PLUGIN_INLINE_PRINT_TEST := plugin/test_inline_print.v
PLUGIN_INLINE_PRINT_EXPECTED := plugin/test_inline_print.expected
PLUGIN_INLINE_PRINT_OUTPUT := /tmp/rocqofrust-plugin-inline-print.out

PLUGIN_PACKAGES := \
	rocq-runtime.clib,rocq-runtime.config,rocq-runtime.engine,rocq-runtime.interp,rocq-runtime.kernel,rocq-runtime.lib,rocq-runtime.library,rocq-runtime.parsing,rocq-runtime.pretyping,rocq-runtime.printing,rocq-runtime.proofs,rocq-runtime.tactics,rocq-runtime.vernac
PLUGIN_ML := plugin/link_model.ml plugin/link_render.ml plugin/rocqofrust_link_plugin.ml

TRANSLATED_ADD_ONE_VO := examples/default/examples/custom/evaluate/translated_add_one.vo
TRANSLATED_ADD_ONE_EXTRACTED := evaluate/extracted/translated_add_one
TRANSLATED_ADD_ONE_BINARY := /tmp/rocqofrust-translated-add-one
TRANSLATED_CHOOSE_AND_ADD_VO := examples/default/examples/custom/evaluate/translated_choose_and_add.vo
TRANSLATED_CHOOSE_AND_ADD_EXTRACTED := evaluate/extracted/translated_choose_and_add
TRANSLATED_CHOOSE_AND_ADD_BINARY := /tmp/rocqofrust-translated-choose-and-add

default: all

plugin: plugin/rocqofrust_link_plugin/rocqofrust_link_plugin.cmxs

plugin/rocqofrust_link_plugin/rocqofrust_link_plugin.cmxs: $(PLUGIN_ML) plugin/rocqofrust_link_plugin/META
	mkdir -p plugin/rocqofrust_link_plugin
	ocamlfind ocamlopt -I plugin -package $(PLUGIN_PACKAGES) -linkall -shared $(PLUGIN_ML) -o $@

plugin-inline-print-check: plugin $(PLUGIN_INLINE_PRINT_TEST) $(PLUGIN_INLINE_PRINT_EXPECTED)
	@echo "COQC plugin inline print $(PLUGIN_INLINE_PRINT_TEST)"
	@coqc -R . RocqOfRust -I plugin -impredicative-set $(PLUGIN_INLINE_PRINT_TEST) > $(PLUGIN_INLINE_PRINT_OUTPUT)
	@diff -u $(PLUGIN_INLINE_PRINT_EXPECTED) $(PLUGIN_INLINE_PRINT_OUTPUT)

evaluate-translated-examples: evaluate-translated-add-one evaluate-translated-choose-and-add

evaluate-translated-add-one: $(TRANSLATED_ADD_ONE_VO)
	coqc -R . RocqOfRust -I plugin -impredicative-set \
		examples/default/examples/custom/evaluate/translated_add_one.v
	ocamlfind ocamlopt -thread -package rocq-runtime.kernel \
		-c $(TRANSLATED_ADD_ONE_EXTRACTED).mli
	ocamlfind ocamlopt -thread -package rocq-runtime.kernel \
		-I evaluate/extracted \
		-c $(TRANSLATED_ADD_ONE_EXTRACTED).ml
	ocamlfind ocamlopt -thread -package rocq-runtime.kernel -linkpkg \
		-I evaluate/extracted \
		$(TRANSLATED_ADD_ONE_EXTRACTED).cmx \
		-o $(TRANSLATED_ADD_ONE_BINARY)
	@$(TRANSLATED_ADD_ONE_BINARY)
	@echo "Translated add_one(41) evaluated to 42."

evaluate-translated-choose-and-add: $(TRANSLATED_CHOOSE_AND_ADD_VO)
	coqc -R . RocqOfRust -I plugin -impredicative-set \
		examples/default/examples/custom/evaluate/translated_choose_and_add.v
	ocamlfind ocamlopt -thread -package rocq-runtime.kernel \
		-c $(TRANSLATED_CHOOSE_AND_ADD_EXTRACTED).mli
	ocamlfind ocamlopt -thread -package rocq-runtime.kernel \
		-I evaluate/extracted \
		-c $(TRANSLATED_CHOOSE_AND_ADD_EXTRACTED).ml
	ocamlfind ocamlopt -thread -package rocq-runtime.kernel -linkpkg \
		-I evaluate/extracted \
		$(TRANSLATED_CHOOSE_AND_ADD_EXTRACTED).cmx \
		-o $(TRANSLATED_CHOOSE_AND_ADD_BINARY)
	@$(TRANSLATED_CHOOSE_AND_ADD_BINARY)
	@echo "Translated choose_and_add(true, (10, 20), 5) evaluated to 15."

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
