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
else
  RUNTIME = mono
endif

INCLUDE=--include $(ARCH) --include $(REPO_BASE)/src/crypto/poly1305/x64/
Z3_OPTIONS=--z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false
VALE_ARITH_REPR=--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped
FSTAR_OPTIONS=$(INCLUDE) $(Z3_OPTIONS) --hint_info --debug yes --max_fuel 0 --max_ifuel 0 --z3rlimit_factor 4 $(VALE_ARITH_REPR)
VALE=$(RUNTIME) $(REPO_BASE)/bin/vale.exe

all: poly1305.v test

test: test-poly1305
	make -C $(ARCH) all

vale:
	cd $(REPO_BASE); scons --NOVERIFY

$(ARCH)/decls.fst: $(ARCH)/decls.vaf
	$(VALE) -in $(ARCH)/decls.vaf -fstarText -out $(ARCH)/decls.fst

poly1305.fst: poly1305.vaf $(ARCH)/decls.vaf
	$(VALE) -in poly1305.vaf -fstarText -out poly1305.fst

poly1305.v: poly1305.fst $(ARCH)/decls.fst
	fstar $(FSTAR_OPTIONS) poly1305.fst

$(ULIB_ML)/fstarlib.cmxa:
	$(MAKE) -C $(ULIB_ML)

.PHONY: test-poly1305
test-poly1305: poly1305.exe
	./$<

MISSING_ML=$(addprefix $(ULIB_ML)/extracted/,FStar_Map.ml)
MY_ML=$(addprefix out/,FStar_Seq_Base.ml FStar_BitVector.ml FStar_UInt.ml Semantics.ml Vale.ml Decls.ml Print.ml Poly1305.ml)

# Approximation
$(MY_ML): $(wildcard *.fst)
	$(FSTAR) $(FSTAR_DEFAULT_ARGS) $(INCLUDE) --lax --odir out --codegen OCaml poly1305.fst

poly1305.exe: $(ULIB_ML)/fstarlib.cmxa $(MISSING_ML) $(MY_ML)
	$(OCAMLOPT) -I out $^ -o $@

clean:
	make -C $(ULIB_ML) clean
	rm -rf out
	rm -f *~
