Vale (Verified Assembly Language for Everest)
=============================================

Vale is a tool for constructing formally verified high-performance assembly language code,
with an emphasis on cryptographic code.
It uses existing verification frameworks,
such as [Dafny](https://github.com/Microsoft/dafny) and [F\*](https://github.com/FStarLang/FStar),
for formal verification.
It supports multiple architectures, such as x86, x64, and ARM, and multiple platforms, such as Windows, Mac, and Linux.
Additional architectures and platforms can be supported with no changes to the Vale tool.

Vale is part of the [Everest project](https://project-everest.github.io).

# Installation

See the [INSTALL](./INSTALL.md) file for installing Vale and its dependencies.

# Code Organization

See the [CODE](./CODE.md) file for more details on the various files in the repository.

For cryptography implementations verified with Vale/F*, see [HACL*](https://github.com/project-everest/hacl-star/tree/fstar-master/vale).  
For cryptography implementations verified with Vale/Dafny, see the [Dafny legacy branch](https://github.com/project-everest/vale/tree/legacy_dafny).  

# Documentation

See the [Vale documentation](./doc/index.html) for a description of the Vale language and Vale tool.

You can also see our academic papers describing Vale:

* [Vale: Verifying High-Performance Cryptographic Assembly Code](https://project-everest.github.io/assets/vale2017.pdf)  
Barry Bond, Chris Hawblitzel, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch, Bryan Parno, Ashay Rane, Srinath Setty, Laure Thompson. In Proceedings of the USENIX Security Symposium, 2017. Distinguished Paper Award.
* [A Verified, Efficient Embedding of a Verifiable Assembly Language](https://www.microsoft.com/en-us/research/publication/a-verified-efficient-embedding-of-a-verifiable-assembly-language/)  
Aymeric Fromherz, Nick Giannarakis, Chris Hawblitzel, Bryan Parno, Aseem Rastogi, Nikhil Swamy. In Proceedings of the Symposium on Principles of Programming Languages (POPL), 2019.

# License

Vale is licensed under the Apache license in the [LICENSE](./LICENSE) file.

# Version History
- v0.1:   Initial code release, containing code written by:
Andrew Baumann, Barry Bond, Andrew Ferraiuolo, Chris Hawblitzel,
Jon Howell, Manos Kapritsos, K. Rustan M. Leino, Jacob R. Lorch,
Bryan Parno, Ashay Rane, Srinath Setty, and Laure Thompson.
