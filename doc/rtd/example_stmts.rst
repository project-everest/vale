::

    assume x < 10;
    assert x <= 10;
    assert x <= 10 implies p(x) by
    {
        myLemma(x);
    }
    forall (x:int, y:int)
        x < y implies x <= y by
    {
        myLemma2(x, y);
    }

::

    // copy eax into immutable x:
    let x := eax;
    // let x be an alias for eax:
    let x @= eax;
    // mutable x:
    ghost var x:uint32 := 33 + 44;
    // ask solver to find an x:
    let exists (x:int) 0 <= x;

::

    reveal myOpaqueFunction;
    reveal myOpaqueFunction(5, x);

::

    Increment(x);
    // declare x and y:
    let (x:int, y) := MyProc(ebx, z);
    // declare x and update y:
    (let x:int), y := MyProc(ebx, z);
    x := 5;

::

    while (eax != 0)
        invariant true;
        decreases *;
    { ... }

::

    if (eax != 5)
    {
        Increment(edx);
    }
    else
    {
        eax := 0;
    }
