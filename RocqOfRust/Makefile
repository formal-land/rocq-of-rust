.PHONY: all clean clean-util distclean default watch generate jinja plugin links-explicit links-expanded-check

VFILES := $(shell find -L . -name "*.v" | grep -v -f blacklist.txt | sort)
JINJA_TEMPLATES := $(shell find -L . -name "*.v.jinja2" | sort)
JINJA_GENERATED := $(JINJA_TEMPLATES:.v.jinja2=.v)
EXPANDED_LINK_ROOT := ../expanded-links/RocqOfRust
LINK_PLUGIN_SUPPORT_SOURCES := \
	links/RocqOfRust.v
LINK_PLUGIN_SOURCES := \
	core/links/cmpOrdering.v
LINK_EXPAND_SOURCES := $(LINK_PLUGIN_SUPPORT_SOURCES) $(LINK_PLUGIN_SOURCES)

PLUGIN_PACKAGES := \
	rocq-runtime.clib,rocq-runtime.config,rocq-runtime.engine,rocq-runtime.interp,rocq-runtime.kernel,rocq-runtime.lib,rocq-runtime.library,rocq-runtime.parsing,rocq-runtime.pretyping,rocq-runtime.printing,rocq-runtime.proofs,rocq-runtime.tactics,rocq-runtime.vernac
PLUGIN_ML := plugin/link_model.ml plugin/link_render.ml plugin/rocqofrust_link_plugin.ml
EXPANDER_ML := plugin/link_model.ml plugin/link_render.ml plugin/link_expand_main.ml

default: all

jinja: $(JINJA_GENERATED)

plugin: plugin/rocqofrust_link_plugin/rocqofrust_link_plugin.cmxs

plugin/rocqofrust_link_plugin/rocqofrust_link_plugin.cmxs: $(PLUGIN_ML) plugin/rocqofrust_link_plugin/META
	mkdir -p plugin/rocqofrust_link_plugin
	ocamlfind ocamlopt -I plugin -package $(PLUGIN_PACKAGES) -linkall -shared $(PLUGIN_ML) -o $@

plugin/link_expand: $(EXPANDER_ML)
	ocamlfind ocamlopt -I plugin $(EXPANDER_ML) -o $@

links-explicit: plugin/link_expand $(LINK_EXPAND_SOURCES)
	./plugin/link_expand $(EXPANDED_LINK_ROOT) $(LINK_EXPAND_SOURCES)

links-expanded-check: links-explicit
	@echo "COQC expanded links/RocqOfRust.v"
	@cd $(EXPANDED_LINK_ROOT) && coqc -R . "" -R ../../RocqOfRust RocqOfRust -impredicative-set links/RocqOfRust.v
	@for file in $(LINK_PLUGIN_SOURCES); do \
		echo "COQC expanded $$file"; \
		cd $(EXPANDED_LINK_ROOT) && coqc -R . "" -R ../../RocqOfRust RocqOfRust -impredicative-set $$file; \
	done

# We use the '@' to avoid displaying this command as the parameters list is
# very long.
RocqMakefile: plugin $(VFILES) blacklist.txt
	@coq_makefile -f _RocqProject -o $@ $(VFILES)

MAKEROCQ := +$(MAKE) -f RocqMakefile

%.v: %.v.jinja2 scripts/macros.jinja2 scripts/jinja_preprocess.py
	python scripts/jinja_preprocess.py $<

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
