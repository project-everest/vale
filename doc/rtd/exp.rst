.. highlight:: vale


Types, functions, and expressions
=================================

As mentioned in :ref:`programs`, a Vale program contains a series of top-level declarations.
These top-level declarations may be:

* type declarations and operand type declarations
* global variable declarations
* ``const`` and ``function`` declarations
* procedure declarations
* verbatim blocks (see :ref:`verbatim`)

Vale processes declarations in the order they appear in the program.
The order matters,
because each declaration can refer to earlier declarations but not later declarations.
All declared names (types, variables, constants, functions, procedures)
live in a single namespace:
you cannot have a type, a function, and a procedure with the same name.
For any name ``x``, there may be up one non-``extern`` top-level declaration named ``x``
or multiple ``extern`` declarations named ``x``.
If two top-level ``extern`` declarations with the same name are declared,
the later declaration hides the earlier one.

For compatibility with Dafny modules and FStar modules,
names may contain ``.`` symbols, as in ``FStar.Pervasives.option``.

Global variables, constants, functions, and procedures have types.
Vale has a simple type system with polymorphism but without dependent types.
Because Vale's type system is simpler than that of some verification frameworks, such as FStar's,
there may be expressions from the verification framework that
Vale's type system cannot type-check.
As described in the next section, a Vale program can use type casts to access such expressions.
For formal details on Vale's type system,
see `here <https://raw.githubusercontent.com/project-everest/vale/master/doc/types.txt>`_.


.. _types:

Types
-----

Vale has a small number of built-in types
and can import other types from the underlying verification framework.
The ``type x ... extern`` declaration imports types from the verification framework:

::

    type char:Type(0) extern;
    type option(a:Type(0)):Type(0) extern;
    type map(a:Type(0), b:Type(0)):Type(0) extern;

Types can have type parameters like ``a:Type(0)``.
For example, the map type shown above takes parameters ``a`` and ``b``,
which can be instantiated with types:

::

    let x:map(int, option(bool)) := ...;

Every type declaration specifies a *kind* for each type parameter and a return kind.
The most common kind is ``Type(0)``, and for Dafny, ``Type(0)`` is the only kind that is needed.
However, FStar is more complicated does not allow all types to have the same kind.
FStar's ``prop`` type, for example, has kind ``Type(1)``.
Therefore, Vale also supports kinds ``Type(1)``, ``Type(2)``, and so on.

Vale provides the following built-in primitive types:

* ``bool``, containing constants ``true`` and ``false``
  and used for operators like ``&&``, ``||``, and ``==>``.
* ``prop`` (FStar only), which FStar uses instead of ``bool`` for ``forall`` and ``exists``.
  Vale uses the same constants ``true`` and ``false``
  and ``&&``, ``||``, and ``==>`` for ``prop`` as for ``bool``,
  and will automatically generate the appropriate FStar operators
  as necessary (e.g. generating FStar's ``/\`` or ``&&`` from Vale's ``&&`` as appropriate).
  In Vale, ``bool`` is a subtype of ``prop``, so values of type ``bool``
  can be used where a value of type ``prop`` is expected.
* ``int``, containing all mathematical integers ..., (-2), (-1), 0, 1, 2, ...
* ``int_range(I1, I2)``, containing integers in the range I1...I2 (including I1 and I2).
  ``I1`` and ``I2`` must be integer constants or the symbol ``_``,
  representing no bound (i.e. negative or positive infinity).
  For example, if ``x`` has type ``int_type(0, _)``,
  then ``x + 1`` will have type ``int_type(1, _)``.
  Smaller range types are subtypes of larger range types and of ``int``,
  so that a value of type ``int_type(1, _)`` can be used where
  a value of type ``int_type(0, _)`` or ``int`` is expected.
* ``tuple(t1, ..., tn)`` is the type of tuples containing components
  of type ``t1`` ... ``tn``, created by expressions ``tuple(e1, ..., en)``.
* ``fun(t1, ..., tn) -> t0`` is type of functions accepting arguments
  of type ``t1`` ... ``tn`` and returning type ``t0``.

In addition, Vale is aware of the following types,
although they must be declared explicitly as ``type x ... extern;`` declarations
with a {:primitive} attribute (see :ref:`attributes`):

* ``state``, the type of the program's state (the built-in expression ``this`` has type ``state``)
* ``string``, the type of string literals
* ``list(t)`` (FStar only), the type of list literals ``list(e1, ..., en)``
* ``seq(t)`` (Dafny only), the type of sequence literals ``seq(e1, ..., en)``
* ``set(t)`` (Dafny only), the type of set literals ``set(e1, ..., en)``

The ``type x ... := ...;`` syntax declares type abbreviations:

::

    type my_bool:Type(0) := bool;
    type nat:Type(0) := int_range(0, _);
    type pos:Type(0) := int_range(1, _);
    type byte:Type(0) := int_range(0, 0xff);
    type int_map(a:Type(0)):Type(0) := map(int, a);

Within Vale's type system, type abbreviations like ``nat`` are equivalent to the types
that they abbreviate, like ``int_range(0, _)``.
When generating Dafny/FStar code, Vale attempts to preserve abbreviations,
so that if variable ``x`` has type ``nat`` in the Vale code,
it will have type ``nat`` in the Dafny or FStar code, not ``int_range(0, _)``.
Vale will not generate a declaration of the ``nat`` type itself,
so ``nat`` must be declared manually in separate Dafny or FStar code.
Also note that raw ``int_range`` types do not have built-in equivalents in Dafny and FStar:
``int_range`` is translated into ``int`` in Dafny and into refinements of ``int`` in FStar.

``extern`` procedures and functions can be polymorphic over types:

::

    ghost procedure g1#[a:Type(0), b:Type(0)](ghost x:a, ghost y:b)
        extern;

    ghost procedure g2()
    {
        g1(10, true);
        g1#[int, bool](10, true);
    }

The explicit type arguments ``#[int, bool]`` are optional;
without them, Vale will try to infer type arguments.

The syntax ``#t(e)`` or ``#(t)(e)`` casts expression ``e`` to type ``t``:

::

    ghost procedure cast_test(ghost i:int)
        requires
            i >= 0;
    {
        let n:nat := #nat(i);
    }

The cast in this example is needed because ``i``'s type ``int`` is not a subtype of ``n``'s type ``nat``.

Although Vale does not have dependent types,
it has some limited support for interacting with some of FStar's dependent types:

::

    type buf_typ:Type(0) extern;
    const bt32:buf_typ extern;
    const bt64:buf_typ extern;
    type buf(bt:Dependent(buf_typ)):Type(0) extern;
    type buf32:Type(0) := buf(dependent(bt32));
    type buf64:Type(0) := buf(dependent(bt64));
    function buf_len #[bt:Dependent(buf_typ)](b:buf(bt)):int extern;

If an expression ``xe`` has type ``xt``, then the type ``dependent(xe)`` has kind ``Dependent(xt)``.
In the example above, this allows
type ``buf`` to take a value ``bt`` as a type parameter
and allows ``buf_len`` to be polymorphic over values ``bt`` of type ``buf_typ``,
as in a dependent type system.
(From Vale's perspective, ``bt`` is promoted to a type in order to use ordinary polymorphism over types.)
However, ``xe`` must be a global constant and ``xt`` must be simple named type,
so this is only useful in limited situations.


Operands and operand types
--------------------------

Vale expressions have types, while procedure operands have *operand types*.
Operand types describe both the type of the value carried by the operand (e.g. an integer)
and the location of the operand.
Locations may be global variables (typically registers), constants,
or dynamically constructed locations (typically memory addresses).
Here is an example of operand type declarations for x64 assembly language:

::

    type nat64:Type(0) := int_range(0, 0xffff_ffff_ffff_ffff);

    operand_type reg64:nat64 :=
    | inout rax | inout rbx | inout rcx | inout rdx
    | inout rsi | inout rdi | inout rbp | inout r8
    | inout r9 | inout r10 | inout r11 | inout r12
    | inout r13 | inout r14 | inout r15
    ;

    operand_type shift_amt64:nat64 := in rcx | const;
    operand_type Mem64(in base:reg64, inline offset:int):nat64;
    operand_type dst_opr64:nat64 := reg64 | Mem64;
    operand_type opr64:nat64 := dst_opr64 | const;

This declares a series of operand types:

* operand type ``reg64``, for 64-bit values (of type ``nat64``) located in registers ``rax`` ... ``r15``,
  usable as both input and output operands.
* operand type ``shift_amt64``, for x64 shift instructions that require the shift amount
  in either register ``rcx`` or as a constant.
* operand type ``Mem64``, for 64-bit values located in memory.
* operand type ``dst_opr64``, for operands that can be either a register or memory operand
* operand type ``opr64``, for operands that can be either a register, memory operand, or constant.
  (Note that ``const`` is a built-in Vale keyword, not an operand type.)

For example, an x64 shift-left instruction can be declared to take
a destination operand of operand type ``dst_opr64`` and a source operand
of type ``shift_amt64``:

::

    procedure Shl64(inout dst:dst_opr64, in amt:shift_amt64)


Operand constructors and memory
^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Locations can be constructed dynamically with *operand constructors* like ``Mem64``.
Such constructors can take other operands as arguments:

::

    Shl64(Mem64(rax, 60), 16);

Each operand constructor requires *operand procedures* for reading and/or writing the location
specified by the operand constructor.
The operand procedures have the name of the operand constructor concatenated
with the suffix "_in" or "_out":

::

    var mem:map(int, byte) {:state mem()};

    procedure Mem64_in(in base:reg_opr64, inline offset:int) returns(o:operand)
        {:operand}
        reads
            mem;
        extern;

    procedure Mem64_out(in base:reg_opr64, inline offset:int, in o:operand)
        {:operand}
        modifies
            mem;
        extern;

In the first procedure, the operand ``o`` contains the value loaded from memory.
In the second procedure, the operand ``o`` contains the value being stored to memory.
Operand procedures can optionally have ``requires`` and ``ensures`` to specify
properties of ``o`` and of the other parameters to the procedures.
Operand procedures can also read and write global variables like ``mem``.


.. _locations:

Operand values and locations
^^^^^^^^^^^^^^^^^^^^^^^^^^^^

Vale procedures can refer to both the value and location of an operand.
For an operand parameter ``x``, the expression ``x`` contains the operand's value,
while the expression ``@x`` contains the operand's location.
This can be used, for example, to require two operands to be in distinct registers:

::

    procedure IncrTwo(inout dst1:reg64, inout dst2:reg64)
        requires
            dst1 < 100;
            dst2 < 100;
            @dst1 != @dst2;
        ensures
            dst1 == old(dst1) + 1;
            dst2 == old(dst2) + 1;
    {
        Add(dst1, 1);
        Add(dst2, 1);
    }

To use ``@x``, ``x``'s operand type must declare a type for locations, using the ``@ t`` syntax.
The following declaration, for example, tells Vale that the expressions ``@dst1`` and ``@dst2``
should have type ``operandImpl``:

::

    operand_type reg64:nat64 @ operandImpl :=
    | inout rax | inout rbx | inout rcx | inout rdx
    ...



.. _functions:

Functions and consts
--------------------

Vale can import functions and constants from the verification framework
using ``const x ... extern`` and ``function x ... extern`` declarations:

::

    const seven:int extern;

    function sum3(x:int, y:int, z:int):int extern;

    function sqr(x:int):(z:int)
        ensures
            z >= 0;
        extern;

    function id#[a:Type(0)](x:a):a extern;

    ghost procedure test_functions()
    {
        assert seven == 7;

        assert sum3(10, 20, 30) == 60;
        assert sqr(10) == 100;
        assert id(10) == 10;
        assert id#[int](10) == 10;

        let f:fun(int, int, int) -> int := sum3;
        assert f(10, 20, 30) == 60;

        let g:fun(int) -> int := id;
        assert g(10) == 10;
    }

Polymorphic functions like ``id`` can be applied to type arguments using ``#[...]``;
otherwise, Vale will try to infer the type arguments.
Monomorphic functions have function types ``fun(...) -> ...``;
polymorphic functions can be coerced to monomorphic function types,
as with ``g`` in the example above.

Dafny and FStar can declare *opaque* functions whose definitions are hidden from the verifier
unless explicitly revealed.
Vale can reveal an opaque function's definition with ``reveal f``:

::

    function opaque_sum(x:int, y:int):int extern;

    ghost procedure test_opaque()
    {
        reveal opaque_sum;
        assert opaque_sum(10, 20) == 30;
    }


.. _custom:

Custom operators
^^^^^^^^^^^^^^^^

Vale programs can abbreviate one-argument and two-argument functions as custom unary and binary operators.
Such operators are not overloaded --- there can only be one function for each operator name ---
but Vale programs can create as many operator names as desired.

The :ref:`lexical` section describes how to use the ``#token`` directive to create new operator names (operator tokens).
After creating a name, the Vale code declares a function abbreviation using the
``function operator(...) ... := ...`` syntax:

::

    #token #+# precedence +
    #token +. precedence +
    #token *. precedence *
    #token %. precedence *
    #token ~~ precedence !
    function operator(#+#) (a:int, b:int):int := opaque_sum;
    function operator(+.) (a:poly, b:poly):poly := poly_add;
    function operator(*.) (a:poly, b:poly):poly := poly_mul;
    function operator(%.) (a:poly, b:poly):poly := poly_mod;
    function operator(~~) (a:quad32):poly := quad32_to_poly;

    ghost procedure test_opaque()
    {
        reveal opaque_sum;
        assert 10 #+# 20 == 30;
    }


.. _overloaded:

Overloaded operators
^^^^^^^^^^^^^^^^^^^^

Vale supports a small set of overloadable operators:

* ``.fieldname`` for reading a field of a datatype
* ``.fieldname :=`` for updating a field of a datatype with some value
* ``[]`` for reading an item in a collection based on some key
* ``[ := ]`` for updating an item in a collection based on some key and value
* ``?[]`` for testing whether a collection contains a key

Each of these operators can have many implementations.
Each implementation is declared to Vale with a ``function operator(...) ... extern`` declaration:

::

    type int_pair:Type(0) extern;
    function Mkint_pair(fst:int, snd:int):int_pair extern;

    function operator(.fst) (p:int_pair):int extern;
    function operator(.snd) (p:int_pair):int extern;
    function operator(.fst :=) (p:int_pair, v:int):int_pair extern;
    function operator(.snd :=) (p:int_pair, v:int):int_pair extern;

    type seq(a:Type(0)):Type(0) extern;
    type map(a:Type(0), b:Type(0)):Type(0) extern;

    function length#[a:Type(0)](s:seq(a)):nat extern;

    function operator([])     #[a:Type(0)](s:seq(a), i:int):a extern;
    function operator([ := ]) #[a:Type(0)](s:seq(a), i:int, v:a):seq(a) extern;
    function operator([])     #[a:Type(0), b:Type(0)](m:map(a, b), key:a):b extern;
    function operator([ := ]) #[a:Type(0), b:Type(0)](m:map(a, b), key:a, v:b):map(a, b) extern;
    function operator(?[])    #[a:Type(0), b:Type(0)](m:map(a, b), key:a):bool extern;

    ghost procedure test_overload(ghost s:seq(nat), ghost m:map(int, nat))
        requires
            length(s) > 3;
    {
        let x := Mkint_pair(10, 20);
        assert x.fst == 10;
        assert x.snd == 20;
        let x2 := x.(fst := 11);
        assert x2.fst == 11;
        assert x2.snd == 20;

        let s2:seq(nat) := s[3 := 30];
        assert s2[3] == 30;

        assert m?[100] ==> m[100] >= 0;
    }

When an expression like ``m[100]`` uses an overloaded operator like ``operator([])``,
Vale must decide which of the various ``operator([])`` implementations is appropriate.
To do this, it computes the type ``t`` of ``m``, simplifies ``t`` until it is an ``extern`` type
rather than a type abbreviation, and then uses ``t``'s name (``map`` in this case) for disambiguation.
Thus, there can be one ``operator([])`` for ``map`` and one for ``seq``,
but not more than one for ``map`` or more than one for ``seq``.


Expressions
-----------

See the :ref:`syntax` section for a complete list of Vale expressions.
The following expressions are described in other sections:

* ``@x`` in :ref:`locations`
* ``old`` in :ref:`procedures`
* function application in :ref:`functions`
* field and subscript operators in :ref:`overloaded`
* collection and tuple literals in :ref:`types`

Arithmetic operators ``*``, ``/``, ``%``, ``+``, and ``-``
compute new ``int`` and ``int_range`` values from existing ``int`` and ``int_range``
values (see :ref:`types` or
the `formal type rules <https://raw.githubusercontent.com/project-everest/vale/master/doc/types.txt>`_).
Integer comparison operators ``<``, ``>``, ``<=``, and ``>=``
compute ``bool`` values from ``int`` and ``int_range`` values.

Comparisons can be chained together: ``a <= b < c <= d`` is an abbreviation for
``a <= b && b < c && c <= d``.

Equality ``==`` and inequality ``!=`` compute ``bool`` values (in Dafny)
or ``prop`` values (in FStar).

``e is C`` tests whether a datatype value ``e`` is an instance of datatype constructor ``C``
(like Dafny's ``e.C?`` or FStar's ``C? e``).

Logical operators ``!``, ``&&``, ``||``, ``==>``, ``<==``, and ``<==>``
compute ``bool`` values from existing ``bool`` values in Dafny.
For FStar, they work on both ``bool`` and ``prop`` values.

``if e1 then e2 else e3`` selects either ``e2`` or ``e3`` based on ``e1`` of type ``bool``.

``let x := e1 in e2`` introduces a variable ``x``, equal to ``e1``, in ``e2``.

``fun(x1:t1, ..., xn:tn) e``, sometimes known as a "lambda", creates an anonymous function
with parameters ``x1`` ... ``xn`` and body ``e``.

``this`` computes the current state (i.e. all register values, memory values, etc.),
of type ``state``.
The ``state`` type is not defined by Vale,
but is instead user-defined in the underlying verification framework
(see ``va_state`` in :ref:`interface`).
Most procedures shouldn't refer to ``this``, but it is occasionally used for
implementing instructions (see :ref:`instructions`),
which can read ``this`` or assign ``this := ...``.


.. _quantifiers:

Quantifiers
^^^^^^^^^^^

Vale supports two *quantifiers*, ``forall`` and ``exists``.
The expression ``forall(x1:t1, ..., xn:tn) e`` means that ``e``
is true for all values that can be assigned to variables ``x1`` ... ``xn``
of type ``t1`` ... ``tn``.
The expression ``exists(x1:t1, ..., xn:tn) e`` means that ``e``
is true for at least one assignment of values to variables ``x1`` ... ``xn``
of type ``t1`` ... ``tn``.
In Dafny, ``forall`` and ``exists`` expressions have type ``bool``.
In FStar, they have type ``prop``.

``forall`` and ``exists``, used in combination with
other expressions like arithmetic and function application,
are often difficult for verification frameworks to reason about
completely automatically.
Specifically, it's hard for the verification framework to answer these two questions:

* If the verifier knows ``forall(x1:t1, ..., xn:tn) e`` and wants to use this to
  prove some formula ``Q``, which values should it instantiate ``x1`` ... ``xn``
  with?  For example, if it knows ``forall(x:int) p(x + x) == x + x + x``,
  which ``x`` should it choose to prove ``p(10) == 15``?
  (In this example, ``x = 5`` is a good choice,
  but it's not obvious how a verifier should guess this automatically.)
* If the verifier wants to prove ``exists(x1:t1, ..., xn:tn) e``,
  which values for ``x1`` ... ``xn`` should it choose to prove ``e``?
  For example, it can prove ``exists(x:int) 2 * x == x + 10`` with ``x = 10``,
  but it's not obvious how to guess this automatically,
  especially in more complicated examples.

Dafny and FStar rely on ``triggers`` (also called patterns)
to determine how to use ``forall`` expressions and how to prove ``exists``
expressions.
For example, suppose the verifier knows ``forall(x:int, y:int) f(x, y) == x + y``
and wants to prove ``f(2, 3) == 5``.
This can be proven with ``x = 2``, ``y = 3``, which the verifier can guess
by matching the expression ``f(x, y)`` with the expression ``f(2, 3)``.
To enable this matching, a Vale program annotates the ``forall`` expression with the *trigger*
``{f(x, y)}``, which tells the verifier to try to find terms of the form ``f(..., ...)``
and match them to ``f(x, y)``:

::

    forall(x:int, y:int){f(x, y)} f(x, y) == x + y

A trigger can have more than one expression in it;
the trigger fires if all the expressions in the trigger are matched:

::

    forall(x:int, y:int){f(x), g(y))} f(x) == g(y)

There can also be more than one trigger; the verifier tries to match any of them.

Dafny will automatically infer the triggers shown in the examples above,
so the Vale code can safely omit them.
However, FStar will not infer them, so it's a good idea to always write the triggers explicitly when using FStar.
(Without the triggers, FStar lets the underlying SMT solver choose the triggers,
and these triggers tend to be dangerously aggressive, leading to slow proofs and timeouts.)

Even when using Dafny, not all quantified expressions have good triggers.
The expression ``forall(x:int) p(x + x) == x + x + x``, for example,
cannot be matched with ``p(10) == 15`` to produce ``x = 5`` in any obvious way,
since ``p(10) == 15`` doesn't contain ``5`` anywhere.
Dafny's automatic inference of triggers doesn't help, since there is no good trigger to infer.
Therefore, it's wise to use quantified expressions that have good triggers.
For example, the expression ``forall(y:int) y % 2 == 0 ==> p(y) == y / 2 * 3`` can use ``{p(y)}``
as a trigger (and Dafny will infer this trigger automatically).
This is logically equivalent to the earlier expression,
but enables better automation.

There are two other questions relevant to quantifiers (the flip side of the
two earlier questions):

* How does a verifier prove ``forall(x1:t1, ..., xn:tn) e``?
* How does a verifier use ``exists(x1:t1, ..., xn:tn) e`` to prove some formula ``Q``?

Compared with the two earlier questions, these are relatively easy and do not require triggers.
For example, a verification framework can prove ``forall(x1:t1, ..., xn:tn) e`` simply
by trying to prove ``e`` with variables ``x1`` ... ``xn`` in scope.
There is no need to instantiate ``x1`` ... ``xn`` with particular values to do this,
so there is no decision to make on which values to instantiate ``x1`` ... ``xn`` with.
However, ``e`` itself could be difficult to prove, and the verification framework
may need hints to complete the proof of ``e``, such as calls to lemmas.
Vale programs can use a ``forall`` statement to supply such hints:

::

    function f1(x:int, y:int):bool extern;
    function f2(x:int, y:int):bool extern;

    ghost procedure lemma_f1_f2(ghost x:int, ghost y:int)
        requires
            f1(x, y);
        ensures
            f2(x, y);
        extern;

    ghost procedure test_forall()
        ensures
            forall(x:int, y:int){f1(x, y)}{f2(x, y)} f1(x, y) ==> f2(x, y);
    {
        forall (x:int, y:int){f2(x, y)}
            f1(x, y) implies f2(x, y) by
        {
            lemma_f1_f2(x, y);
        }
    }

In this example, the ``forall (x:int, y:int)...{...}`` statement proves
``forall(x:int, y:int){f2(x, y)} f1(x, y) ==> f2(x, y)``,
which in turn proves ``test_forall``'s postcondition.

For ``exists``, a ``let exists`` statement (Dafny-only, not FStar)
can extract variables from an ``exists`` expression in order to use
those variables to prove other expressions, such as the precondition to
``lemma_f1_f2`` in the following example:

::

    ghost procedure test_exists()
        requires
            exists(x:int, y:int){f1(x, y)} f1(x, y);
    {
        // Ask verifier to choose some x and y such that f1(x, y):
        let exists (x:int, y:int){f1(x, y)} f1(x, y);
        // Now we have x and y as local ghost variables and we can use them:
        lemma_f1_f2(x, y);
    }
