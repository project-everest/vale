#define FSTAR_HOME in Makefile.inc
include Makefile.inc
REPO_BASE=../../../../..
ARCH=$(REPO_BASE)/tools/Vale/test

ifeq ($(OS),Windows_NT)
  RUNTIME =
  SCONS = scons.bat
  FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe --smt $(FSTAR_HOME)/bin/z3.exe
else
  RUNTIME = mono
  SCONS = scons
  FSTAR_EXE = fstar
endif

INCLUDE=--include $(ARCH) --include $(REPO_BASE)/src/crypto/poly1305/x64/
FSTAR_OPTIONS=$(INCLUDE) --hint_info --debug yes --smtencoding.elim_box true

VALE=$(RUNTIME) $(REPO_BASE)/bin/vale.exe

# For simplified Makefiles, define FSTAR_HOME, then include the file below.
include $(FSTAR_HOME)/examples/Makefile.include

all: ocaml

vale: 
	cd $(REPO_BASE); $(SCONS) bin/Vale.exe

include $(FSTAR_HOME)/ulib/ml/Makefile.include

$(ARCH)/decls.fst: $(ARCH)/decls.vaf
	$(VALE) -in $(ARCH)/decls.vaf -fstarText -outi $(ARCH)/decls.fsti -out $(ARCH)/decls.fst

machine: $(ARCH)/Machine.fst
	$(FSTAR_EXE) $(FSTAR_OPTIONS) --eager_inference $(ARCH)/Machine.fst

semantics: $(ARCH)/Machine.fst
	$(FSTAR_EXE) $(FSTAR_OPTIONS) --eager_inference $(ARCH)/Semantics.fst

print: $(ARCH)/Machine.fst
	$(FSTAR_EXE) $(FSTAR_OPTIONS) $(ARCH)/Print.fst

declsi: $(ARCH)/Machine.fst $(ARCH)/Semantics.fst $(ARCH)/decls.fst
	$(FSTAR_EXE) $(FSTAR_OPTIONS) --eager_inference $(ARCH)/decls.fsti

decls: $(ARCH)/Machine.fst $(ARCH)/Semantics.fst $(ARCH)/decls.fst
	$(FSTAR_EXE) $(FSTAR_OPTIONS) --eager_inference $(ARCH)/decls.fst

poly1305.fst: poly1305.vaf $(ARCH)/decls.vaf
	$(VALE) -in poly1305.vaf -fstarText -out poly1305.fst

poly1305.v: poly1305.fst $(ARCH)/decls.fst
	$(FSTAR_EXE) $(FSTAR_OPTIONS) --eager_inference poly1305.fst

ocaml: out poly1305.fst $(ARCH)/decls.fst
	$(MAKE) -C $(ULIB_ML)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(INCLUDE) --lax --odir out --codegen OCaml poly1305.fst
	$(OCAMLOPT) -I $(FSTAR_HOME)/ulib/ml/extracted/ out/FStar_Map.ml out/Semantics.ml out/Decls.ml out/Vale.ml out/Poly1305.ml -o poly1305.exe
	./poly1305.exe

out:
	mkdir -p out

clean:
	make -C $(ULIB_ML) clean
	rm -rf out
	rm -f *~
