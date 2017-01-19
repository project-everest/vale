module Collections__Sets_i {

lemma lemma_subset_cardinality<T>(s:set<T>, s':set<T>)
    requires s <= s';
    requires |s| == |s'|;
    ensures s == s';
{
    if s == {} {
    } else {
        var x :| x in s;
        lemma_subset_cardinality(s - {x}, s' - {x});
    }
}

ghost method pick_unused_int(s:set<int>) returns (x:int)
    ensures x !in s;
{
    var i := 0;
    var excluded := {};
    while i < |s| 
        invariant 0 <= i <= |s|;
        invariant forall e :: e in excluded ==> e in s;
        invariant forall e :: 0 <= e < |excluded| ==> e in excluded;
        invariant forall e :: e < 0 || e >= i ==> e !in excluded;
        invariant |excluded| == i;
        invariant excluded <= s;
    {
        if i !in s {
            return i;
        } else {
            assert i !in excluded;
            excluded := excluded + { i };
        }
        i := i + 1;
    }
    lemma_subset_cardinality(excluded, s);
    assert excluded == s;
    return i + 1;
}

} // end module Collections__Sets_i

