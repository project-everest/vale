.. highlight:: vale

Introduction
============

Vale is a language and tool for developing verified low-level code:

* **Language and tool.**
  Vale code is written in a C-style syntax.
  The Vale tool translates Vale code into a form that may be verified and executed.
* **Verified code.**
  Vale supports Hoare-logic style reasoning with preconditions, postconditions, and loop invariants.
* **Low-level code.**
  Vale is designed for verifying code at the level of assembly language or register-transfer languages.
  It is not designed to support higher-level features such as complex expression evaluation, object orientation, or higher-order functions.
  It does, however, support basic control constructs such as if/else statements, while loops, and procedure calls.

Vale does not perform verification by itself,
but instead relies on existing verification framework.
Currently, Vale can use `Dafny <https://github.com/dafny-lang/dafny>`_
or `FStar <https://www.fstar-lang.org/>`_ for verification.
Vale programs may import definitions and lemmas provided by the underlying
verification framework.
Since these definitions and lemmas vary between frameworks,
Vale program written for one verification framework may not be verifiable
by another framework.

For source code, binary releases, installation instructions,
and links to academic papers about Vale,
see the `Vale GitHub repository <https://github.com/project-everest/vale>`_.
