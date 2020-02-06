.. highlight:: vale


.. _programs:

Programs and procedures
=======================

A Vale program consists of a series of top-level declarations,
including global variable declarations and procedure declarations.
For example, the following Vale program defines global variables and procedures to
represent simple assembly language code on a hypothetical x86-like architecture:

::

    var ok:bool {:state ok()};
    var eax:int {:state reg(EAX)};
    var ebx:int {:state reg(EBX)};

    procedure IncrEax()
        modifies
            eax;
        requires
            0 <= eax < 100;
        ensures
            eax == old(eax) + 1;
        extern;

    procedure Test()
        modifies
            eax; ebx;
        requires
            0 <= eax < 99;
        ensures
            eax == old(eax) + 2;
            ebx == old(ebx);
    {
        IncrEax();
        IncrEax();
    }

The global variables ``eax`` and ``ebx`` represent two assembly language registers,
each containing a value of type ``int``.
(The type ``int`` contains all mathematical integers;
a more realistic assembly language would use a type for 32-bit integers or 64-bit integers.)
The global variable ``ok`` represents the status of the running program:
``ok == true`` means the program is
in a good state, and ``ok == false`` means that the program has crashed.
The ``IncrEax`` procedure represents an assembly language instruction that
increments register ``eax``; the ``extern`` keyword
indicates that the procedure's body is defined elsewhere.
The body of the ``Test`` procedure represents assembly language code that calls ``IncrEax`` twice,
adding 2 to ``eax``.


.. _procedures:

Procedures
----------

Vale procedures consist of parameter and return value declarations,
specifications (``reads``, ``modifies``, ``requires``, ``ensures``, and ``lets``),
and, for non-``extern`` procedures, a body containing statements.
Statements may include calls to procedures, ``if``/``else`` statements, and ``while`` statements:

::

    procedure TestControl()
        modifies
            eax;
        requires
            0 <= eax < 100;
        ensures
            eax == 100;
    {
        if (eax < 50)
        {
            IncrEax();
            IncrEax();
        }

        while (eax < 100)
            invariant
                0 <= eax <= 100;
            decreases
                100 - eax;
        {
            IncrEax();
        }
    }

If a procedure modifies a global variable, it must declare that it ``modifies`` the variable.
If a procedure reads a global variable, it must declare that it ``reads`` or ``modifies`` the variable.

To verify properties of a program, procedures can ``require`` preconditions and ``ensure`` postconditions.
If verification is successful, then after executing a procedure, the procedure's postcondition will be true,
assuming the precondition was true before executing the procedure.
The procedure ``TestControl``, for example, guarantees that if ``eax`` is in the range 0...99 upon entry,
then ``eax`` will be 100 upon exit.
When preconditions refer to global variables, such as ``eax``, they describe the initial value of the global variable
upon entry to procedure.
Postconditions, on the other hand, describe the final values of global variables as the procedure exits.
Postconditions may refer to the initial state using the expression ``old(...)``.
For example, ``IncrEax``'s postcondition ``eax == old(eax) + 1`` specifies that
the value of ``eax`` upon exit equals the value upon entry (``old(eax)``) plus one.

By default, all procedures implicitly say ``modifies ok; requires ok; ensures ok;``,
so that all procedures ensure that the program doesn't crash.

Verification of a procedure may be automatic or may require hints from the program.
For example, ``while`` loops require a loop invariant as a hint to guide the verification process.
The invariant must be true upon entry to the loop and is verified to be true after each loop iteration.
The loop invariant shown above, for example, guarantees ``0 <= eax <= 100`` after each iteration.
Notice that the loop condition ``eax < 100`` must be false when the loop exits,
so after the loop exits, the verifier knows both ``0 <= eax <= 100`` and ``!(eax < 100)``,
which together imply ``eax == 100``, satisfying the procedure's postcondition.
Also notice that the loop condition ``eax < 100`` must be true inside the loop body.
Together with the the invariant ``0 <= eax <= 100``, this implies ``IncrEax``'s
precondition ``0 <= eax < 100``.

Vale can also prove that programs terminate (don't go into an infinite loop).
For this, ``while`` loops need to specify an expression that decreases towards
some lower bound, such as 0.  This expression must strictly decrease in each loop iteration.
In the example above, ``100 - eax`` decreases in each iteration, since ``eax`` increases in each iteration.
If termination isn't required, the while loop can specify ``decreases *;``, which allows infinite loops.


Macros and instructions
-----------------------

The ``IncrEax`` procedure shown above is of limited use since it can only modify a single register
and can only add exactly 1 to the register.
For more flexibility, procedures can accept operands as parameters:

::

    operand_type reg:int := inout eax | inout ebx;
    operand_type opr:int := reg | const;

    procedure Add(inout x:reg, in y:opr)
        ensures
            x == old(x + y);
        extern;

    procedure TestAdd()
        modifies
            eax; ebx;
        requires
            0 <= eax < 99;
        ensures
            eax == old(eax) + 30;
            ebx == old(ebx) - 30;
    {
        Add(eax, 10);
        Add(eax, 20);
        Add(ebx, (-30));
    }

The ``Add`` procedure accepts two operand arguments, ``x`` and ``y``,
where ``y`` is an input operand (read-only) and ``x`` is both input and output (read and/or written).
Each operand has an operand type.
``x``'s operand type ``reg`` specifies that ``x`` may be instantiated with
either ``eax`` or ``ebx``, for reading and/or writing, and that ``x`` contains a value of type ``int``.
``y``'s operand type ``opr`` extends ``reg`` to also allow for constants as operands, such as the ``10``
passed by ``TestAdd``.

Procedures with operand parameters can represent assembly language instructions,
as in the ``Add`` procedure shown above.
They can also represent assembly language macros,
as the following ``AddThree`` procedure demonstrates:

::

    procedure AddThree(inout x:reg)
        ensures
            x == old(x + 3);
    {
        Add(x, 1);
        Add(x, 2);
    }

    procedure TestThree()
        modifies
            eax; ebx;
        requires
            0 <= eax < 99;
        ensures
            eax == old(eax) + 6;
            ebx == old(ebx) + 3;
    {
        AddThree(eax);
        AddThree(eax);
        AddThree(ebx);
    }

Calls from one procedure to another are inlined during assembly language printing,
so that ``TestThree``'s body is equivalent to:

::

    Add(eax, 1);
    Add(eax, 2);
    Add(eax, 1);
    Add(eax, 2);
    Add(ebx, 1);
    Add(ebx, 2);


Inline parameters and recursive macros
--------------------------------------

Operand parameters allow procedures to vary the operands passed to their instructions,
but procedures can also vary the instructions themselves.
This allows for macros whose instructions are configurable.
The key to this configuration is ``inline`` parameters,
which can have any type and can be used by ``inline if`` statements
to decide whether to generate certain sequences of instructions.
For example, the following procedure ``AddMaybeThree`` uses an inline parameter ``b`` of type ``bool``
to decide whether to generate an ``Add(x, 2)`` instruction when printing the assembly language output:

::

    procedure AddMaybeThree(inline b:bool, inout x:reg)
        ensures
            x == old(x) + (if b then 3 else 1);
    {
        Add(x, 1);
        inline if (b)
        {
            Add(x, 2);
        }
    }

    procedure TestMaybeThree()
        modifies
            eax; ebx;
        requires
            0 <= eax < 99;
        ensures
            eax == old(eax) + 3;
            ebx == old(ebx) + 1;
    {
        AddMaybeThree(true, eax);
        AddMaybeThree(false, ebx);
    }

In this example, ``TestMaybeThree``'s body results in the following sequence of instructions:

::

    Add(eax, 1);
    Add(eax, 2);
    Add(ebx, 1);

While an ordinary ``if (e)`` instruction generates compare and branch instructions to
test the condition ``e`` at runtime, an ``inline if (e)`` instruction resolves the condition ``e``
statically, when printing the assembly language code.
Because of this, the condition ``e`` cannot depend on runtime state.
Instead, ``e`` usually consists of constants (as in ``true`` and ``false`` in ``TestMaybeThree``),
or expressions computed from other inline parameters.

One example of using inline parameters and ``inline if`` is to vary instructions across different platforms,
such as Windows and Unix.  An ``inline if`` can generate prolog and epilog code customized to each platform
based on an inline parameter that specifies the platform.

Another use of ``inline if`` is generating repetitive sequences of instructions.
The following ``Add2N`` procedure generates two ``Add`` instructions and then recursively
calls itself to generate more instructions:

::

    procedure Add2N(inline n:int, inout x:reg)
        {:recursive}
        requires
            n >= 0;
        ensures
            x == old(x + 3 * n);
    {
        inline if (n > 0)
        {
            Add(x, 1);
            Add(x, 2);
            Add2N(n - 1, x);
        }
    }

    procedure TestAdd2N()
        modifies
            eax;
        requires
            0 <= eax < 99;
        ensures
            eax == old(eax) + 9;
    {
        Add2N(3, eax);
    }

Since the recursive call, like other calls, is inlined during code generation,
this has the effect of generating a long sequence of unrolled instructions:

::

    Add(eax, 1);
    Add(eax, 2);
    Add(eax, 1);
    Add(eax, 2);
    Add(eax, 1);
    Add(eax, 2);

(Note that recursive procedures require an attribute ``{:recursive}`` to call themselves;
without this, Vale would not consider the ``Add2N``'s name to be in scope inside ``Add2N``'s body.
Vale does not support mutually recursive procedures.)


Ghost variables and ghost code
------------------------------

The examples so far have shown very simple ``requires``, ``ensures``, and ``invariant`` expressions.
When writing more complex preconditions, postconditions, and invariants,
it often helps to define abbreviations for complex expressions.
These abbreviations can be placed in *ghost* variables that are used to assist the proof but have no
effect on the program's runtime behavior.
The simplest way to introduce a ghost variable is with ``let``:

::

    procedure Ghosts1()
        requires
            eax == 0;
        modifies
            eax; ebx;
        ensures
            ebx == old(ebx) + 100;
    {
        let lo := ebx;
        let hi := lo + 100;
        while (eax < 100)
            invariant
                lo <= ebx <= hi;
                ebx == lo + eax;
            decreases
                100 - eax;
        {
            Add(eax, 1);
            Add(ebx, 1);
        }
    }

The variable ``lo`` holds a copy of the contents of ``ebx`` upon entry to the procedure,
and ``hi`` holds ``lo + 100``.
The loop invariant may refer to ``lo`` and ``hi`` to indicate that ``ebx`` stays
in the range ``lo`` ... ``hi`` through all loop iterations.
Physical (non-ghost) variables like ``eax`` may be assigned to ghost variables,
but ghost variables cannot be assigned to physical variables.
For example, ``Add(eax, lo)`` is not allowed, since the ghost variable ``lo``
exists only during verification, not when the assembly language code is run,
and so ``lo`` cannot be used as an assembly language instruction operand.

It's often convenient to share ghost variables across procedure specifications and the procedure body.
The ``lets`` specification introduces ghost variables that are in scope
both in the remaining specifications (``ensures ebx == hi``) and in the procedure body:

::

    procedure Ghosts2()
        lets
            lo := ebx;
            hi := lo + 100;
        requires
            eax == 0;
        modifies
            eax; ebx;
        ensures
            ebx == hi;
    {
        while (eax < 100)
            invariant
                lo <= ebx <= hi;
                ebx == lo + eax;
            decreases
                100 - eax;
        {
            Add(eax, 1);
            Add(ebx, 1);
        }
    }

``lets`` declarations evaluate global variables in the procedure's initial state.
In the example above, ``hi`` contains the initial value of ``ebx``,
and ``ensures ebx == hi`` compares the final ``ebx`` to ``hi``, which contains the initial ``ebx`` plus 100.
Thus, ``lets`` can be used as an alternative to ``old(...)`` for refering to the initial state.

Ghost variables introduced with ``let`` and ``lets`` are immutable.
Mutable ghost variables are introduced with ``ghost var``; these may be assigned by ``:=`` statements:

::

    procedure Ghosts3()
        requires
            eax == 0;
        modifies
            eax; ebx;
        ensures
            ebx == old(ebx) + 100;
    {
        let lo := ebx;
        let hi := lo + 100;
        ghost var countdown:int := 100;

        while (eax < 100)
            invariant
                lo <= ebx <= hi;
                ebx == lo + eax;
                countdown == 100 - eax;
            decreases
                countdown;
        {
            Add(eax, 1);
            Add(ebx, 1);
            countdown := countdown - 1;
        }
    }

The statement ``countdown := countdown - 1;`` is an example of ghost code,
which is only used to assist verification and does not appear in generated assembly language code.
Ghost code can also contain:

* calls to ghost procedures, such as lemmas
* ``assert`` statements
* ``assume`` statements
* ``ghost if`` statements
* ``calc`` statements
* ``reveal`` statements (see :ref:`functions`)
* ``forall`` and ``exists`` statements (see :ref:`quantifiers`)

*Ghost procedures* can only contain ghost code.
They cannot read or modify global variables.
The following somewhat silly example illustrates operations by ghost code on ghost variables:

::

    ghost procedure ghost_example(ghost x:int) returns(ghost y:int)
        requires
            10 <= x;
        ensures
            20 <= y;
    {
        y := x;
        y := y + x;
        ghost if (x > 100)
        {
            y := y + 1;
        }
        assert 20 <= y; // not necessary; for illustration purposes only
    }

Note that ghost parameters, like ``x``, are immutable while ghost return values, like ``y``,
are mutable.

The ``ghost if`` statement is like an ordinary ``if`` statement except that it has no runtime
effect and its body can only contain ghost code.

The ``assert`` statement asks the underlying verification framework to verify
that an expression is true; if the expression is false, verification will fail.
This can be used for documentation and diagnostics.
``assert`` statements can occassionally act as hint to the underlying verification framework:
if a proof relies on ``forall (x) ...f(x)...`` expressions for which the verification framework
needs hints on how to instantiate the quantified variable ``x``,
``assert f(10)``, for example can serve as a hint to instantiate ``x`` with 10
(see :ref:`quantifiers`).
(Such hints can be abused: if a proof seems to need a long series of
seemingly arbitrary ``assert`` statements to succeed,
it's often a sign that the proof needs to be restructured in a clearer way.)

In contrast to ``assert``, which just asks the verifier to check a property,
``assume`` demands that the verifier accept a property without proof.
This can be useful when debugging proofs: you can assume part of a proof to
test if that assumption enables the rest of the proof to succeed.
Of course, ``assume`` is dangerous since it allows proofs of false theorems,
so after debugging a proof, all ``assume`` statements should be removed.

``extern`` ghost procedures can represent lemmas from the underlying verification framework
(Dafny or FStar).
This allows longer proofs about mathematics, datatypes, functions, etc. to reside
in Dafny or FStar libraries rather than requiring that all proofs be done directly in Vale.

The following example illustrates calls to ghost procedures.
The code assumes that two lemmas about arithmetic,
``lemma_commute_mul`` and ``lemma_square_plus_minus_half``,
have already been proven in the underlying verification framework:

::

    ghost procedure lemma_commute_mul(ghost x:int, ghost y:int)
        ensures
            x * y == y * x;
        extern;

    ghost procedure lemma_square_plus_minus_half(ghost x:int)
        ensures
            x * (x + 1) / 2 == x * (x - 1) / 2 + x;
        extern;

    procedure ArithmeticSum(ghost n:int)
        modifies
            eax; ebx;
        requires
            0 <= n;
            ebx == 0;
            eax == n;
        ensures
            ebx == n * (n + 1) / 2;
    {
        while (0 < eax)
            invariant
                0 <= eax;
                ebx + eax * (eax + 1) / 2 == n * (n + 1) / 2;
            decreases
                eax;
        {
            lemma_square_plus_minus_half(eax);
            lemma_commute_mul(eax, eax - 1);
            Add(ebx, eax);
            Add(eax, (-1));
        }
    }

The calls to lemmas serve as hints to help prove that the loop invariant remains true
after each loop iteration.
Whether such hints are necessary depends on underlying verification framework
and the difficulty of the properties being verified.
Simple properties may not require any hints,
while more advanced properties may require extensive lemmas.

Notice that the procedures above declare ``ghost`` parameters.
Such parameters may be instantiated with physical expressions or ghost expressions.
(The ``ghost n:int`` parameter to ``ArithmeticSum`` is for illustration;
a simpler alternative would be to declare ``lets n := eax`` rather than forcing
the caller of ``ArithmeticSum`` to supply ``n`` as an argument.)

Verification can take advantage of lemma postconditions,
such as ``ensures x * y == y * x``.
To make verification faster, it often helps to limit the scope of such postconditions
so that they are only used to prove relevant facts and don't add overhead when proving
unrelated facts.
Vale provides two features for limiting the scope of postconditions: ``assert by`` and ``calc``.
The following code shows another way to write the loop body of ``ArithmeticSum``,
where the lemmas are used only to prove ``b' + a' * (a' + 1) / 2 == n * (n + 1) / 2``
and nothing else:

::

    {
        let b' := ebx + eax;
        let a' := eax - 1;
        assert b' + a' * (a' + 1) / 2 == n * (n + 1) / 2 by
        {
            lemma_square_plus_minus_half(eax);
            lemma_commute_mul(eax, eax - 1);
        }

        Add(ebx, eax);
        Add(eax, (-1));
    }

For even more clarity and efficiency, the ``calc`` statement can break a proof
into a series of small steps,
proving some relation (typically equality, ``==``) between each step:

::

    {
        let a := eax;
        let b := ebx;
        let b' := b + a;
        let a' := a - 1;
        calc ==
        {
            b' + a' * (a' + 1) / 2;
            ==
            b + a' * (a' + 1) / 2 + a;
            ==
            b + (a - 1) * a / 2 + a;
            == {lemma_commute_mul(a - 1, a);}
            b + a * (a - 1) / 2 + a;
            == {lemma_square_plus_minus_half(a);}
            b + a * (a + 1) / 2;
            ==
            n * (n + 1) / 2;
        }

        Add(ebx, eax);
        Add(eax, (-1));
    }

The syntax ``calc ==`` indicates that the calc statement proves the initial
expression (``b' + a' * (a' + 1) / 2``) equal to the final expression
(``n * (n + 1) / 2``).
Each ``==`` inside the ``calc`` statement marks a single step,
proving the expression above the ``==`` equal to the expression below the ``==``.
A ``calc`` statement can use ghost code, such as lemma calls, to help prove each step.
This ghost code lives inside ``{...}`` after the ``==``,
as in ``{lemma_commute_mul(a - 1, a);}`` above.
``calc`` statements often provide clearer documentation to people reading the code
than unstructured series of calls to lemmas.
However, if ``calc`` statements or ``assert by`` statements start to become large,
it's often a good idea to move the proof steps into the underlying verification framework
so that the Vale code can focus solely on verifying assembly language operations.

``assert by`` statements can also contain preconditions that are required
inside the body of the ``assert by`` statement:

::

    ghost procedure lemma_cube_positive(ghost x:int)
        requires
            0 <= x;
        ensures
            0 <= x * x * x;
        extern;

    ghost procedure test_cube_positive()
        reads
            eax;
        ensures
            0 <= eax ==> 0 <= eax * eax * eax;
    {
        assert 0 <= eax implies 0 <= eax * eax * eax by
        {
            lemma_cube_positive(eax);
        }
    }

In this case, the ``assert by`` statement proves that ``0 <= eax * eax * eax``
is true if ``0 <= eax`` is true.
(Without the ``0 <= eax`` condition, the call to ``lemma_cube_positive``
would fail because ``eax`` might be negative.)


Global variable aliases
-----------------------

Procedures can use ``lets`` declarations to introduce local aliases (alternate names)
for global variables:

::

    procedure TestAddAlias()
        lets
            a @= eax; b @= ebx;
        modifies
            a; b;
        requires
            0 <= a < 99;
        ensures
            a == old(a) + 30;
            b == old(b) - 30;
    {
        Add(a, 10);
        Add(a, 20);
        Add(b, (-30));
    }

In contrast to ``lets a := eax``, which introduces an immutable ghost variable ``a``
holding a copy of ``eax``'s initial value,
``lets a @= eax`` introduces a mutable alias for ``eax``.
``a`` can be used interchangeably with ``eax`` in the specification and body of the procedure ``TestAddAlias``.


.. _includes:

Modules and includes
--------------------

Vale files can ``include`` declarations from other Vale files.
Suppose, for example, that file ``b.vad`` includes file ``a.vad``:

::

    include "a.vad"

In this case, ``a.vad``'s declarations will appear as ``extern`` declarations to ``b.vad``.

Vale tries to find the file ``a.vad`` in the same directory as ``b.vad``.
If the files are in different directories, the ``include`` directive can use a path relative to ``b.vad``:

::

    include "../../d/a.vad"

As an alternative to looking for the file relative to ``b.vad``'s directory,
the ``include`` directive can supply a named *path alias*.
Vale will then try to find the file relative to the path associated with this alias:

::

    include{:from STDLIB} "d/a.vad"

The path for the alias (e.g. ``STDLIB``) is defined with command-line arguments (see :ref:`attributes` and :ref:`tool`).

When Vale generates Dafny code, the generated code may need to include other Dafny files.
Rather than using a verbatim block for this (see :ref:`verbatim`),
the Vale file can use a verbatim include, which is translated into a Dafny include in the generated Dafny code:

::

    include{:verbatim} "vale.dfy"
    include{:verbatim} "vale64.dfy"
    include{:verbatim}{:from BASE} "code/lib/util/operations.dfy"
    include "decls.vad"

Vale code may have to refer to definitions from FStar module,
which use qualified names like ``FStar.Seq.seq`` or ``X64.Machine_s.state``.
The current best way to do this is with ``include{:fstar}{:open}``,
specifying the FStar *module name* (not the filename):

::

    include{:fstar}{:open} "X64.Machine_s"
    include{:fstar}{:open Sequence} "FStar.Seq"
    ...
    const s:state extern; // state refers to X64.Machine_s.state
    const q:Sequence.seq extern; // Sequence.seq refers to FStar.Seq.seq

Using the ``{:open}`` attribute,
Vale code refers to FStar names without the module prefix (e.g. without ``X64.Machine_s.``).
Using the ``{:open x}`` attribute,
Vale code refers to FStar names with an alternate module prefix ``x`` (e.g. ``Sequence.``).

Every generated FStar file needs a module declaration.
Rather than using a verbatim block for this (see :ref:`verbatim`),
the Vale file can use a Vale module declaration:

::

    module A
