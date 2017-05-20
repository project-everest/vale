# Makefile.inc should define FSTAR
include Makefile.inc

VALE = ..\..\bin\vale.exe
Z3 = z3-2017-05-06.exe
EXPZ = src\bin\Debug\ExperimentZ3.exe

FSTAR_ARGS = --smt $(Z3) --eager_inference --print_fuels --max_fuel 1 --max_ifuel 1 --z3rlimit 20 --z3cliopt smt.QI.EAGER_THRESHOLD=100 --z3cliopt smt.CASE_SPLIT=3 --z3cliopt smt.arith.nl=false
Z3_ARGS = -smt2 smt.QI.EAGER_THRESHOLD=100 smt.CASE_SPLIT=3 smt.arith.nl=false

$(EXPZ): src\ast.fs src\main.fs src\lex.fsl src\parse.fsy
	MSBuild.exe .\src\ExperimentZ3.sln
	editbin /stack:128000000 $(EXPZ)

..\..\obj\Vale\test\decls_alt.fst: ..\Vale\test\decls_alt.vaf
	$(VALE) -fstarText -conciseLemmas=false -in ..\Vale\test\decls_alt.vaf -out ..\..\obj\Vale\test\decls_alt.fst

..\..\obj\thirdPartyPorts\OpenSSL\poly1305\x64\poly1305_alt.fst: ..\..\src\thirdPartyPorts\OpenSSL\poly1305\x64\poly1305_alt.vaf ..\Vale\test\decls_alt.vaf
	$(VALE) -fstarText -assumeUpdates 3 -conciseLemmas=false -in ..\..\src\thirdPartyPorts\OpenSSL\poly1305\x64\poly1305_alt.vaf -out ..\..\obj\thirdPartyPorts\OpenSSL\poly1305\x64\poly1305_alt.fst

decls_alt: ..\Vale\test\Semantics_alt.fst ..\Vale\test\Vale_alt.fst ..\..\obj\Vale\test\decls_alt.fst
	$(FSTAR) $(FSTAR_ARGS) ..\Vale\test\Semantics_alt.fst ..\Vale\test\Vale_alt.fst ..\..\obj\Vale\test\decls_alt.fst --verify_module Decls_alt

poly1305_alt: ..\Vale\test\Semantics_alt.fst ..\Vale\test\Vale_alt.fst ..\..\obj\Vale\test\decls_alt.fst ..\..\obj\thirdPartyPorts\OpenSSL\poly1305\x64\poly1305_alt.fst
	$(FSTAR) $(FSTAR_ARGS) --log_queries ..\Vale\test\Semantics_alt.fst ..\Vale\test\Vale_alt.fst ..\..\obj\Vale\test\decls_alt.fst ..\..\src\crypto\poly1305\x64\poly1305_lemmas_alt.fst ..\..\obj\thirdPartyPorts\OpenSSL\poly1305\x64\poly1305_alt.fst --verify_module Poly1305_alt

poly1305_mod0: $(EXPZ)
	$(EXPZ) -in .\queries-Poly1305_alt.smt2 -select 2 -stats -print > queries-Poly1305_alt.mod0
	$(Z3) $(Z3_ARGS) queries-Poly1305_alt.mod0

poly1305_mod1: $(EXPZ)
	$(EXPZ) -in .\queries-Poly1305_alt.smt2 -select 2 -remove -stats -print > queries-Poly1305_alt.mod1
	$(Z3) $(Z3_ARGS) queries-Poly1305_alt.mod1

poly1305_phases: $(EXPZ)
	$(EXPZ) -in .\queries-Poly1305_alt.smt2 -select 2 -remove -phase 1 -stats -print > queries-Poly1305_alt.phase1
	$(EXPZ) -in .\queries-Poly1305_alt.smt2 -select 2 -remove -phase 2 -stats -print > queries-Poly1305_alt.phase2
	$(Z3) $(Z3_ARGS) queries-Poly1305_alt.phase1
	$(Z3) $(Z3_ARGS) queries-Poly1305_alt.phase2

