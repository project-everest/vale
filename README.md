
Supplementary Material for *A Verified, Efficient Embedding of A Verifiable Assembly Language*
==============================================================================================

# Organization

[proof.txt] contains a formalization of the interoperation between Low\* and Vale code,
as well as a proof of Theorem 4.2, which demonstrates secret independence for such hybrid programs.

[QuickRegs1.fst] and [QuickRegs2.fst] contain the simplified examples presented in Section 3 as part of the exposition
of our optimized verification technique.


The following directories contain Vale and related tools:

* [tools/Vale/src](./tools/Vale/src): Vale
* [tools/Vale/test](./tools/Vale/test): test files for Vale


The following directories contain library code and cryptographic code verified
by F\* and Vale.  Vale files end in `.vaf`, while F\* files end in `.fsti` for
interfaces and `.fst` for the corresponding implementation.  We generally
distinguish trusted F\* files by appending `_s` (for specification) to the name.

* [src/arch](./src/arch): definitions of basic types 
* [src/arch/x64](./src/arch/x64): definitions and proofs related to our assembly language semantics for x64
    - `X64.Machine_s.fst`: basic components of our machine model
    - `X64.Bytes_Semantics_s.fst`: defines our trusted bytes-level semantics
    - `X64.Vale.Ins*`: implements Vale procedures the provide verified Hoare-style reasoning on top of our semantics
    - `X64.Vale.QuickCode*`: implements our efficient verified verification-condition generator
    - `X64.Taint_Semantics_s.fst`: wraps the basic semantics in a trace-based model of information leakage
    - `X64.Leakage_s.fst`: defines what it means for assembly code to be leakage free
    - `X64.Leakage_i.fst`: implements a verified leakage analyzer
    - `X64.Print_s.fst`: a trusted printer that converts an assembly AST in F\* into assembly suitable for MASM or GCC
    - `Interop.fst`, `Views.fst`, and `interop/` defines interop between Low\* code and Vale code and proves the correctness of various stubs used in our case studies
    - `extracted`: C files extracted from our Low\* code


* [src/lib](./src/lib): general-purpose libraries written in F\*
* [src/crypto](./src/crypto): verified cryptographic code for our Poly1305 and AES case studies
* [src/thirdPartyPorts](./src/thirdPartyPorts): verified cryptographic code, derived from OpenSSL, for Poly1305 

All files verify with F\* version `2634db3e5` and Z3 version 4.5.1.

