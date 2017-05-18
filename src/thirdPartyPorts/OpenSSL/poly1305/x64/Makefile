REPO_BASE=../../../../..
ARCH=$(REPO_BASE)/tools/Vale/test

ifeq ($(OS),Windows_NT)
  RUNTIME =
else
  RUNTIME = mono
endif

INCLUDE=--include $(ARCH) --include $(REPO_BASE)/src/crypto/poly1305/x64/
Z3_OPTIONS=--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false
FSTAR_OPTIONS=$(INCLUDE) $(Z3_OPTIONS) --hint_info --debug yes --max_fuel 0 --max_ifuel 0 --z3rlimit_factor 4
VALE=$(RUNTIME) $(REPO_BASE)/bin/vale.exe

# For simplified Makefiles, define FSTAR_HOME, then include the file below.
include $(FSTAR_HOME)/examples/Makefile.include

all: ocaml

vale: 
	cd $(REPO_BASE); scons --NOVERIFY

include $(FSTAR_HOME)/ulib/ml/Makefile.include

$(ARCH)/decls.fst: $(ARCH)/decls.vaf
	$(VALE) -in $(ARCH)/decls.vaf -fstarText -out $(ARCH)/decls.fst

poly1305.fst: poly1305.vaf $(ARCH)/decls.vaf
	$(VALE) -in poly1305.vaf -fstarText -out poly1305.fst

poly1305.v: poly1305.fst $(ARCH)/decls.fst
	fstar $(FSTAR_OPTIONS) poly1305.fst

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
