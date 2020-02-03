.. highlight:: vale

Complete Vale syntax
====================

This section presents a complete grammar for the Vale language.
The grammar uses the following notation:

* *[* A *]* indicates that A is optional.
* A ... A indicates that A is repeated zero or more times.
* A *[* ... A *]* indicates that A is repeated one or more times.
* Variable/attribute/function/procedure/constructor/field/type/operator-type names are written as
  **x**, **F**, **P**, **C**, **D**, **T**, **O**, where:

  * **F** indicates a function name
  * **P** indicates a procedure name
  * **C** indicates a datatype constructor name
  * **D** indicates a datatype field name
  * **T** indicates a type name
  * **O** indicates an operator type name

* For conciseness, the grammar omits attributes.  Attributes are listed separately, in :ref:`attributes`.

Grammar
-------

+----------------------------------------------------------+-----------------------------------------------------------+
| Grammar                                                  | Examples and notes                                        |
+==========================================================+===========================================================+
| PROGRAM                                                  |                                                           |
|   | INCLUDE ... INCLUDE *[* ``module`` **x** *]*         |                                                           |
|       DECL ... DECL                                      |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| INCLUDE                                                  |                                                           |
|   | ``include`` ``"`` **filename** ``"``                 |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_decl.rst                            | .. include:: example_decl.rst                             |
+----------------------------------------------------------+-----------------------------------------------------------+
| TFORMALS                                                 |                                                           |
|   | TFORMAL ``,`` ... ``,`` TFORMAL                      |                                                           |
| TFORMAL                                                  |                                                           |
|   | **x** ``:`` KIND                                     |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| FORMALS                                                  |                                                           |
|   | FORMAL ``,`` ... ``,`` FORMAL                        |                                                           |
| FORMAL                                                   |                                                           |
|   | **x** *[* ``:`` TYPE *]*                             |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| FRET                                                     |                                                           |
|   | TYPE                                                 |                                                           |
|   | ``(`` **x** ``:`` TYPE ``)``                         |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_pformals.rst                        |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| PRETS                                                    |                                                           |
|   | PRET ``,`` ... ``,`` PRET                            |                                                           |
| PRET                                                     |                                                           |
|   | *[* ``ghost`` *]* **x** ``:`` TYPE                   |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_specs.rst                           | .. include:: example_specs.rst                            |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_stmts.rst                           | .. include:: example_stmts.rst                            |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_calc.rst                            | .. include:: example_calc.rst                             |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_destinations.rst                    | .. include:: example_destinations.rst                     |
+----------------------------------------------------------+-----------------------------------------------------------+
| INVARIANTS                                               |                                                           |
|   | INVARIANT ... INVARIANT                              |                                                           |
| INVARIANT                                                |                                                           |
|   | ``invariant`` EXP ``;`` ... EXP ``;``                |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| DECREASE                                                 |                                                           |
|   | ``decreases`` ``*`` ``;``                            |                                                           |
|   | ``decreases`` EXP *[* ``,`` ... ``,`` EXP *]* ``;``  |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| TRIGGERS                                                 |                                                           |
|   | TRIGGER ... TRIGGER                                  |                                                           |
| TRIGGER                                                  |                                                           |
|   | ``{`` EXP *[* ``,`` ... ``,`` EXP *]* ``}``          |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| INT                                                      |                                                           |
|   | ... | (-2) | (-1) | 0 | 1 | 2 | ...                  |                                                           |
|   | 1_000_000                                            |                                                           |
|   | 0xDeaD_bEEf                                          |                                                           |
|   | ...                                                  |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_exp.rst                             | .. include:: example_exp.rst                              |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_otyps.rst                           |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| TYPE_ARGS                                                |                                                           |
|   | ``#[`` TYPE ``,`` ... ``,`` TYPE ``]``               |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| .. include:: grammar_type.rst                            | .. include:: example_type.rst                             |
+----------------------------------------------------------+-----------------------------------------------------------+
| KIND                                                     |                                                           |
|   | ``Type`` ``(`` 0 ``)`` | ``Type`` ``(`` 1 ``)`` |    |                                                           |
|     ...                                                  |                                                           |
|   | ``Dependent`` ``(`` **t** ``)``                      |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+

.. _verbatim:

Verbatim blocks
---------------

Vale programs may contain verbatim blocks (VERBATIM_DECL_BLOCK in the table above):

::

  #verbatim
  method printCode(...) { ... }
  lemma L(...) { ... }
  #endverbatim

  procedure P()
  {
    L(...);
    ...
  }

  #verbatim
  method Main()
  {
    printHeader();
    var n := printCode(va_code_P(), 0);
    printFooter();
  }
  #endverbatim

Verbatim blocks are written as lines between ``#verbatim`` and ``#endverbatim``.
Vale passes these lines directly to the verification language,
with no processing or analysis by Vale.
For example, verbatim blocks may be used to declare types, functions,
and lemmas in the underlying verification languages so that these
declarations may be used inside Vale procedures.

.. _attributes:

Attributes
----------

Some elements of the Vale grammar may be annotated with *attributes*
that supply additional information to Vale or to the verification language.
Currently, attributes are only supported in the following places:

+----------------------------------------------------------+-----------------------------------------------------------+
| Grammar (attributes)                                     | Examples and notes                                        |
+==========================================================+===========================================================+
| INCLUDE                                                  |                                                           |
|   | ``include`` ATTRIBUTES ``"`` **filename** ``"``      |                                                           |
| DECL                                                     |                                                           |
|   | ...                                                  |                                                           |
|   | ``type`` **T** ... ATTRIBUTES extern ``;``           |                                                           |
|   | ``var`` **x** ``:`` TYPE ATTRIBUTES ``;``            |                                                           |
|   | ``procedure`` **P** ``(`` PFORMALS ``)``             |                                                           |
|   |     ATTRIBUTES                                       |                                                           |
|   |     *[* ``returns`` ... *]* ...                      |                                                           |
|   |     ...                                              |                                                           |
|   | ...                                                  |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| ATTRIBUTES                                               |                                                           |
|   | ATTRIBUTE ... ATTRIBUTE                              |                                                           |
| ATTRIBUTE                                                |                                                           |
|   ``{:`` **x** EXP ``,`` ... ``,`` EXP ``}``             |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+

Currently, the following attributes are supported:

* on include directives:

  * {:from x};
    filename is interpreted relative to the path alias x rather than to the current directory
  * {:verbatim} (Dafny only):
    include a file written directly in the underlying verification language,
    rather than including another Vale file
  * {:fstar} and {:open} (FStar only):
    include a file written directly in FStar,
    rather than including another Vale file,
    and, if {:open} is specified, open the declarations in the file into the Vale namespace

* on procedures:

  * {:timeLimit n} and {:timeLimitMultiplier n} (Dafny only)
    set or increase the time limit for this procedure
  * {:instruction EXP},
    indicating a primitive procedure that is implemented with the code value specified by the expression EXP
  * {:recursive} and {:decrease EXP}, indicating that a procedure may call itself,
    optionally specifying a decreases clause to prove the recursion's termination
  * {:operand}, indicating an operand constructor
  * {:quick} (FStar only) -- an experimental feature that uses a more complicated, but more efficient,
    FStar encoding for generated lemmas

* on global variables:

  * {:state f(EXP, ..., EXP)},
    indicating that the variable **x** corresponds to a field f(EXP, ..., EXP) of the state type.

* on types:

  * {:primitive}, declaring a primitive type like ``state``, ``string``, or ``list``
