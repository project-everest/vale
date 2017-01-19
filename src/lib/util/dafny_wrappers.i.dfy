////////////////////////////////////////////////////////////////////////
//
//  Functions that wrap Dafny primitives so Vale can use them
//
////////////////////////////////////////////////////////////////////////

module dafny_wrappers_i {

    function SeqLength<T>(s:seq<T>) : int { |s| }
    function SeqSlice<T>(s:seq<T>, start:int, end:int) : seq<T>
        requires 0 <= start <= end <= |s|;
        { s[start..end] }
    function SeqTail<T>(s:seq<T>, tail:nat) : seq<T> requires tail <= |s| { s[tail..] }
    function SeqDrop<T>(s:seq<T>, tail:int) : seq<T> 
        requires 0 <= tail <= |s|
        { s[..tail] }
    function SeqAppendElt<T>(s:seq<T>, elt:T) : seq<T> { s + [elt] }
    function SeqBuild<T>(elt:T) : seq<T> { [elt] }
    function SeqRange<T>(s:seq<T>, start:int, end:int) : seq<T>
        requires 0 <= start <= end <= |s|;
        { s[start..end] }

    predicate InSet<T>(x:T, s:set<T>) { x in s }
    predicate InMap<T,S>(x:T, s:map<T,S>) { x in s }

}
