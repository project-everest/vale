::

    lets
        x @= eax;
        y @= ebx;
        z := 3 + 3;
    reads
        x; y;
    requires
        x <= y < z;
        let a := x + y;
        is_even(a);
    ensures
        x == old(x);
        let a := x + y;
        is_even(a);
