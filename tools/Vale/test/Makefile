EVEREST_HOME=../../../..
VALE_ARITH_REPR=--smtencoding.elim_box true --smtencoding.l_arith_repr native --smtencoding.nl_arith_repr wrapped
FSTAR=$(EVEREST_HOME)/FStar/bin/fstar --hint_info --debug yes $(VALE_ARITH_REPR) $(OTHERFLAGS)
VALE=$(EVEREST_HOME)/vale/bin/vale -fstarText

all: Semantics.fst-ver decls.fst-ver Print.fst-ver Vale.fst-ver

%.fst-ver: %.fst
	$(FSTAR) $^

decls.fst-ver: decls.fst
	$(FSTAR) decls.fst --max_fuel 1 --max_ifuel 0 --z3cliopt smt.arith.nl=false $^

%.fst: %.vaf
	$(VALE) -in $^ -out $@
