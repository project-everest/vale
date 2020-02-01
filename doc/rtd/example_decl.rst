::

    type bool:Type(0) extern;
    type my_bool:Type(0) := bool;
    operand_type opr32:nat32 :=
        | inout eax | inout ebx
        | mem32 | const

::

    var x:int;
    const c:int extern;
    function f(x:int, y:int):bool extern;
    function f#[a:Type(0)](x:a):a extern;

::

    procedure P(ghost x:int)
        returns(ghost y:int)
        requires
            0 <= x;
            isEven(x);
        ensures
            x <= y;
        { ... }

::

    #verbatim
    open FStar.Mul
    #endverbatim
