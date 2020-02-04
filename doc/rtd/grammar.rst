.. highlight:: vale


.. _syntax:

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

For FStar code, verbatim blocks can be written to the interface file (``.fsti``)
via ``#verbatim{:interface}``,
the implementation file (``.fst``)
via ``#verbatim`` or ``#verbatim{:implementation}``
or both via ``#verbatim{:interface}{:implementation}``.


.. _lexical:

Lexical structure
-----------------

Single-line comments begin with ``//``.
Longer comments can be placed in ``/*`` ... ``*/``.
Comments can be nested inside each other: ``/* a /* b */ c */`` is a valid comment.
Whitespace includes spaces, newlines, and carriage returns; tab characters are not allowed.

Variable names can include letters, ``_`` characters, ``'`` characters after the first character,
and digits after the first character.
There are special function names ``operator(+)``, ``operator(-)``, etc. to represent operators
in function declarations (see :ref:`functions`).

Vale programs can define new operator tokens
out of the characters
``!`` ``%`` ``+`` ``-`` ``&`` ``^`` ``|`` ``<`` ``>`` ``=`` ``.`` ``#`` ``:`` ``$`` ``?`` ````` ``~`` ``@`` ``\`` ``/``
using the ``#token`` directive:

::

    #token +. precedence +

``#token`` declares a new token (``+.`` in the example above)
that is parsed with the same precedence and associativity as an existing token
(``+`` in the example above).
This token can then be used for a custom operator, as described in :ref:`custom`.


.. _attributes:

Attributes
----------

Some elements of the Vale grammar may be annotated with *attributes*
that supply additional information to Vale or to the verification language.
Currently, attributes are only supported in the following places and
on verbatim blocks:

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
|   |     *[* ``returns`` ... *]* ...                      |                                                           |
|   |     ATTRIBUTES                                       |                                                           |
|   |     SPECS                                            |                                                           |
|   |     ...                                              |                                                           |
|   | ...                                                  |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+
| ATTRIBUTES                                               |                                                           |
|   | ATTRIBUTE ... ATTRIBUTE                              |                                                           |
| ATTRIBUTE                                                |                                                           |
|   ``{:`` **x** EXP ``,`` ... ``,`` EXP ``}``             |                                                           |
+----------------------------------------------------------+-----------------------------------------------------------+

Attributes are not checked by Vale's type checker, so they can contain arbitrary expressions.

Currently, the following attributes are supported:

* on include directives:

  * {:from x};
    filename is interpreted relative to the path alias x rather than to the current directory
    (see :ref:`includes` and :ref:`tool`)
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
    (see :ref:`instructions`)
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

* on verbatim blocks:

  * {:interface} and {:implementation} (FStar only) -- see :ref:`verbatim`


Coding conventions
------------------

The following conventions are recommended (not required) for Vale programs:

* Names

  * Names of non-ghost procedures (including instructions) start with an upper-case letter.
    Names of ghost procedures start with a lower-case letter.
    This helps to distinguish ghost and non-ghost procedure calls.
    Note that for FStar, ghost procedures *must* start with a lower-case letter;
    FStar will reject upper-case ghost procedure names.
  * Names of functions and constants may start with lower-case or upper-case letters,
    depending on the underlying verification framework conventions.
    FStar and Dafny typically use upper-case for datatype constructor functions
    and lower-case for other functions.
  * Names of types and global variables start with lower-case letters.
  * Names of operand types start with a lower-case letter, except for operand constructors,
    which start with an upper-case letter.
  * Names of type parameters and local variables should start with lower-case letters.
    In FStar, this is required.
  * Lower-case names use underscores to separate words: ``my_name``.
    Upper-case names may use underscores: ``MyName`` or ``My_Name`` or ``My_name``.

* Formatting

  * Indentation is 4 spaces.
  * ``//`` is used for single-line comments, ``/* ... */`` for multi-line comments.
  * If a function's parameters or procedure's parameters are too long to fit on a single line,
    the parameters all go on one or more separate lines and are double-indented (8 spaces).
  * Statements and specifications that are too long for a single line are broken into multiple
    lines, with the extra lines indented 4 spaces more than the first line.
  * Binary operators have spaces around them: ``x * y``, ``x / y``, ``x % y``, ``x + y``, ..., ``x <==> y``.
    Colons do not: ``x:int``.  Commas have spaces after them: ``(x, y, z)``..
  * ``if``, ``while``, ``forall``, and ``let exists`` statements have a space before parentheses:
    ``if (...)``, ``while (...)``, ``forall (...)``, ``let exists (...)``.
    In other places, there is no space before parentheses: ``my_lemma(...)``, ``my_function(...)``.
  * Curly brackets ``{`` and ``}``, for multi-line blocks of statements, go on their own line.
    This is largely because ``procedure`` and ``while`` loops have specifications (``requires``, ``invariant``, etc.)
    that get in the way of a ``{`` appearing on the same line as the ``procedure`` or ``while``
    keyword.
  * Each procedure attribute gets its own line.
  * Specification keywords like ``requires``, ``ensures``, ``modifies``, etc. are single-indented
    relative to a procedure or ``while`` loop.
    The specification expressions appear on a separate line from the specification keywords
    and are indented 4 spaces more than the keywords.

Example:

::

    // This is a short procedure
    procedure ShortProc(ghost x:int, ghost y:int)
        modifies
            eax;
    {
        Add(eax, 1);
    }

    /*
    This is a longer procedure.
    Its parameters don't fit on a line, so they are indented 8 spaces.
    */
    procedure MyLongProcedure(
            inline b:bool,
            inout dst:reg, in src:reg,
            ghost apple_banana:bool, ghost cat_dog:int, ghost earth_fire:int)
        {:public}
        {:timeLimit 10}
        modifies
            eax; ebx;
        requires
            10 <= eax < 20;
            ebx == (if apple_banana then cat_dog else
                7 * (earth_fire + src));
    {
        inline if (b)
        {
            while (eax < 100)
                invariant
                    0 <= eax <= 100;
                decreases
                    100 - eax;
            {
                Add(eax, 1);
                MyOtherLongProcedure(b, dst, src, apple_banana, cat_dog,
                    7 * (earth_fire + src), eax, ebx);
                my_lemma(cat_dog);
            }
        }
    }
