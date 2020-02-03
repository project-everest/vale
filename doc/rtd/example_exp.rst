::

    // 3.14159 is a real number

    // bv1, bv2, etc. are bit vectors

    // @x is the location of variable x
    procedure P(in x:opr32)
        requires
            x == 10; // value in x
            @x == OReg(Rax); // x's loc
    {
    }

::

    function f#[a:Type(0)](x:a):a extern;
    assert f(10) == 20; // Vale infers a
    assert f#[int](10) == 20; // explicit

    // cast x to type uint32
    #uint32(x)
    // cast x to type set(uint32)
    #(set(uint32))(x)

::

    // indexing and update
    let s1:seq(int) := f();
    let s2:seq(int) := s1[3 := "hi"];
    assert s2[3] == "hi";
    // Dafny only; like Dafny "10 in m":
    assert m?[10];

::

    old(x)
    old[snapshotOfThis](x)

::

    seq(10, 20, 30) // Dafny only
    set(10, 20, 30) // Dafny only
    list(10, 20, 30) // F* only
    tuple(5, 15, true) // Dafny, F*

::

    //binary operators:
    //  left-associative
    //  but ==> is right-associative
    //
    //highest precedence
      /|\
       | * / %
       | + -
       | < > <= >= is
       | &&
       | ||
       | <== ==>
       | <==>
      \|/
    //lowest precedence

::

    let x := 3 in x + 1

::

    forall(x:int, y:int){foo(x, y)}
        foo(x, y) || x == y
