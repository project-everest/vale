.. highlight:: vale


.. _tool:

Using the Vale tool
===================

We recommend that Vale files have suffix ``.vad`` or ``.vaf``,
the former for Vale code verified with Dafny and the latter for Vale code verified with FStar.
(This is a recommendation, not a requirement.  The Vale tool does not treat any suffixes specially.)

The command-line arguments listed below may be supplied to ``vale.exe``.
At least one of ``-dafnyText``, ``-dafnyDirect``, or ``-fstarText`` is required.
At least on ``-in`` argument is required.
If no ``-out`` argument is given, code is generated to standard output.

**-dafnyText**
  generate a Dafny .dfy file for Dafny to verify

**-dafnyDirect**
  run Dafny directly without generating an intermediate Dafny file

**-fstarText**
  generate an FStar module (a .fst file and a .fsti file) for FStar to verify

**-in <filename.vad>**
  specify one or more input .vad or .vaf files

**-out <filename.dfy>**
  specify the name of the generated .dfy or .fst file

**-outi <filename.fsti>**
  **[FStar only]** specify the name of the generated .fsti file

**-includeSuffix .vad .dfy**
  **[Dafny only]** specify that if ``b.vad`` includes ``a.vad``,
  then the generated ``b.dfy`` file should include ``a.dfy``

**-include <filename.vad>**
  include another .vad or .vaf file (alternative to using ``include`` directives inside the .vad/.vaf files)

**-sourceFrom x path**
  let x be an alias to path in ``include`` directives in source files (see :ref:`attributes` and :ref:`includes`)

**-destFrom x path**
  let x be an alias to path in generated .dfy files
