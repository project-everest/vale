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

