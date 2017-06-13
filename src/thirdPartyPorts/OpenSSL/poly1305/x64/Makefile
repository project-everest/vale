#define FSTAR_HOME in Makefile.inc
-include Makefile.inc
REPO_BASE=../../../../..
ARCH=$(REPO_BASE)/tools/Vale/test

# By default, assume the standard Everest layout... can be overridden via the
# environment.
FSTAR_HOME?=$(REPO_BASE)/../FStar
FSTAR=$(FSTAR_HOME)/bin/fstar.exe
ULIB_ML=$(FSTAR_HOME)/ulib/ml
include $(ULIB_ML)/Makefile.include

ifeq ($(OS),Windows_NT)
  RUNTIME =
  SCONS = scons.bat
  FSTAR_EXE = $(FSTAR_HOME)/bin/fstar.exe
else
  RUNTIME = mono
  SCONS = scons
  FSTAR_EXE = fstar
endif

INCLUDE=--include $(ARCH) --include $(REPO_BASE)/src/crypto/poly1305/x64/
Z3_OPTIONS=--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false
VALE_ARITH_REPR=--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped
FSTAR_OPTIONS=$(INCLUDE) $(Z3_OPTIONS) --hint_info --debug yes --max_fuel 0 --max_ifuel 1 --initial_ifuel 0 --z3rlimit_factor 4 $(VALE_ARITH_REPR)
VALE=$(RUNTIME) $(REPO_BASE)/bin/vale.exe

all: poly1305.v test

test: test-poly1305
	make -C $(ARCH) all

vale: 
	cd $(REPO_BASE); $(SCONS) bin/Vale.exe

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

$(ULIB_ML)/fstarlib.cmxa:
	$(MAKE) -C $(ULIB_ML)

.PHONY: test-poly1305
test-poly1305: poly1305.exe
	./$<

include $(FSTAR_HOME)/ulib/ml/Makefile.include

ocaml: out poly1305.fst $(ARCH)/decls.fst
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(INCLUDE) --lax --odir out --codegen OCaml poly1305.fst --extract_all
	$(OCAMLOPT) -I out -I $(FSTAR_HOME)/ulib/ml/extracted/ out/FStar_Map.ml out/Machine.ml out/Semantics.ml out/Print.ml out/Decls.ml out/Poly1305.ml -o poly1305.exe
	./poly1305.exe

out:
	mkdir -p out

clean:
	make -C $(ULIB_ML) clean
	rm -rf out
	rm -f *~
