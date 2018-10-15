
Artifact for *A Verified, Efficient Embedding of A Verifiable Assembly Language*
==============================================================================================
This [repository](https://github.com/project-everest/vale/tree/popl_artifact_submit) contains 
the version of Vale presented in the POPL 2019 submission *A Verified, Efficient Embedding of A Verifiable Assembly Language*.

For the most recent work on Vale, please look [here](https://github.com/project-everest/vale) for the Vale tool,
and [here](https://github.com/project-everest/hacl-star/tree/fstar-master/vale/) for the Vale cryptographic libraries.

# Organization

[proof.txt](proof.txt) contains a formalization of the interoperation between Low\* and Vale code,
as well as a proof of Theorem 4.2, which demonstrates secret independence for such hybrid programs.

[QuickRegs1.fst](QuickRegs1.fst) and [QuickRegs2.fst](QuickRegs2.fst) contain the simplified examples presented in Section 3 as part of the exposition
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
    - `X64.Vale.Ins*`: implements Vale procedures that provide verified Hoare-style reasoning on top of our semantics
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

All files verify with F\* version `2634db3e5`, KreMLin version `d5afaf72e2` and Z3 version 4.5.1.

# Installation

Vale relies on the following tools, which must be installed before building Vale:

* Python (version 2.x), used by SCons
  * See https://www.python.org/
* SCons, the Python-based build system used by Vale
  * See http://scons.org/
* F\# (version >= 4.0), including [FsLexYacc](http://fsprojects.github.io/FsLexYacc/).  Vale is written in F\#.
  * See http://fsharp.org/ for complete information, including free versions for Windows, Mac, and Linux.
  * FsLexYacc is installed via nuget.exe; see [nuget](https://www.nuget.org/), under "latest nuget.exe"
    * In the Vale root directory, run the command `nuget.exe restore ./tools/Vale/src/packages.config -PackagesDirectory tools/FsLexYacc`
    * This will create a directory tools/FsLexYacc that contains the FsLexYacc binaries; the build will expect to find these binaries in tools/FsLexYacc
* C\#, used by [Dafny](https://github.com/Microsoft/dafny/blob/master/INSTALL)
  * See https://www.visualstudio.com/vs/community/ or http://www.mono-project.com/
* An installed C compiler, used by SCons to compile C files

On an Ubuntu system, including Windows Subsystem for Linux, you can install the dependencies with:
     ```sudo apt install scons fsharp nuget mono-devel```

On Mac OS X (tested with El Capitan, 10.11.6), you can install the dependencies with
    ```brew install scons nuget mono```
Note that the mono package includes F\#.

Once these tools are installed, running SCons in the top-level directory will build the Vale tool and build and verify all the sources in the [src](./src) directory:
* To build all sources in the [src](./src) directory:
  * ```python.exe scons.py --FSTAR-MY-VERSION```
* To build the AES-GCM assembly language and test executable:
  * On Windows, set the `PLATFORM` environment variable to `X64`
  * ```python.exe scons.py --FSTAR-MY-VERSION --FSTAR-EXTRACT obj/aesgcm.asn obj/aesgcm-gcc.S obj/aesgcm-linux.S obj/aesgcm-macos.S```
  * ```python.exe scons.py --FSTAR-MY-VERSION --FSTAR-EXTRACT obj/TestAesGcm.exe```
* To build in parallel, add the `-j` option (e.g. `-j 4` for 4-way parallelism).
  Any warnings about needing `pywin32` can be ignored.
* To see additional generic and Vale-specific options,
  including options to configure where to find Vale, KreMLin, F* and Z3:
  * ```python.exe scons.py --FSTAR-MY-VERSION -h```
* To build in parallel, add the `-j` option (e.g. `-j 4` for 4-way parallelism).
  Any warnings about needing `pywin32` can be ignored.
* To see additional generic and Vale-specific options,
  including options to configure where to find Vale, KreMLin, F* and Z3:
  * ```python.exe scons.py --FSTAR-MY-VERSION -h```
* All the files built and verified will be available in the `obj` directory. To clean the build and reverify everything from scratch, delete the `obj` directory (```rm -r obj```) before running SCons again.
