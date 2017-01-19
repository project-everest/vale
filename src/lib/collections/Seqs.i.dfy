include "Seqs.s.dfy"

module Collections__Seqs_i {

import opened Collections__Seqs_s

function middle<T>(s:seq<T>):seq<T>
    requires |s| >= 2;
    ensures  |middle(s)| == |s| - 2;
    ensures  forall i {:trigger middle(s)[i]} :: 0 <= i < |s| - 2 ==> middle(s)[i] == s[i+1];
{
    s[1..|s|-1]
}

lemma SeqAdditionIsAssociative<T>(a:seq<T>, b:seq<T>, c:seq<T>)
    ensures a+(b+c) == (a+b)+c;
{
}

predicate ItemAtPositionInSeq<T>(s:seq<T>, v:T, idx:int)
{
    0 <= idx < |s| && s[idx] == v
}

lemma Lemma_ItemInSeqAtASomePosition<T>(s:seq<T>, v:T)
    requires v in s;
    ensures  exists idx :: ItemAtPositionInSeq(s, v, idx);
{
    var idx :| 0 <= idx < |s| && s[idx] == v;
    assert ItemAtPositionInSeq(s, v, idx);
}

function FindIndexInSeq<T>(s:seq<T>, v:T):int
    ensures var idx := FindIndexInSeq(s, v);
            if idx >= 0 then
                idx < |s| && s[idx] == v
            else
                v !in s;
{
    if v in s then
        Lemma_ItemInSeqAtASomePosition(s, v);
        var idx :| ItemAtPositionInSeq(s, v, idx);
        idx
    else
        -1
}

lemma Lemma_IdenticalSingletonSequencesHaveIdenticalElement<T>(x:T, y:T)
    requires [x] == [y];
    ensures  x == y;
{
    calc {
        x;
        [x][0];
        [y][0];
        y;
    }
}

//////////////////////////////////////////////////////////
//  Combining sequences of sequences
//////////////////////////////////////////////////////////
function SeqCat<T>(seqs:seq<seq<T>>) : seq<T>
{
    if |seqs| == 0 then []
    else seqs[0] + SeqCat(seqs[1..])
}

function SeqCatRev<T>(seqs:seq<seq<T>>) : seq<T>
{
    if |seqs| == 0 then []
    else SeqCatRev(all_but_last(seqs)) + last(seqs)
}

lemma lemma_SeqCat_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
    ensures SeqCat(A + B) == SeqCat(A) + SeqCat(B);
{
    if |A| == 0 {
    } else {
        calc {
            SeqCat(A + B);
                { assert (A + B)[0] == A[0];  assert (A + B)[1..] == A[1..] + B; }
            A[0] + SeqCat(A[1..] + B);
                { lemma_SeqCat_adds(A[1..], B); }
            A[0] + SeqCat(A[1..]) + SeqCat(B);
            SeqCat(A) + SeqCat(B);
        }
    }
}

lemma lemma_SeqCatRev_adds<T>(A:seq<seq<T>>, B:seq<seq<T>>)
    ensures SeqCatRev(A + B) == SeqCatRev(A) + SeqCatRev(B);
{
    if |B| == 0 {
        assert SeqCatRev(B) == [];
        assert A+B == A;
    } else {
        calc {
            SeqCatRev(A + B);
                { assert last(A + B) == last(B);  assert all_but_last(A + B) == A + all_but_last(B); }
            SeqCatRev(A + all_but_last(B)) + last(B);
                { lemma_SeqCatRev_adds(A, all_but_last(B)); }
            SeqCatRev(A) + SeqCatRev(all_but_last(B)) + last(B);
            SeqCatRev(A) + SeqCatRev(B);
        }
    }
}

lemma lemma_SeqCat_equivalent<T>(seqs:seq<seq<T>>)
    ensures SeqCat(seqs) == SeqCatRev(seqs);
{
    if |seqs| == 0 {
    } else {
        calc {
            SeqCatRev(seqs);
            SeqCatRev(all_but_last(seqs)) + last(seqs);
                { lemma_SeqCat_equivalent(all_but_last(seqs)); }
            SeqCat(all_but_last(seqs)) + last(seqs);
            SeqCat(all_but_last(seqs)) + SeqCat([last(seqs)]);
                { lemma_SeqCat_adds(all_but_last(seqs), [last(seqs)]); 
                  assert seqs == all_but_last(seqs) + [last(seqs)]; }
            SeqCat(seqs);
        }

    }
}

lemma lemma_ElementFromSequenceSlice<T>(s:seq<T>, s':seq<T>, a:int, b:int, pos:int)
    requires 0 <= a <= b <= |s|;
    requires s' == s[a..b];
    requires a <= pos < b;
    ensures  0 <= pos - a < |s'|;
    ensures  s'[pos-a] == s[pos];
{
}

lemma lemma_ElementFromSequencePrefix<T>(s:seq<T>, s':seq<T>, a:int, pos:int)
    requires 0 <= a <= |s|;
    requires s' == s[..a];
    requires 0 <= pos < a;
    ensures  s'[pos] == s[pos];
{
}

lemma lemma_ElementFromSequenceSuffix<T>(s:seq<T>, s':seq<T>, a:int, pos:int)
    requires 0 <= a <= |s|;
    requires s' == s[a..];
    requires a <= pos < |s|;
    ensures  s'[pos-a] == s[pos];
{
}

lemma lemma_SeqSliceOfSlice<T>(s:seq<T>, s1:int, e1:int, s2:int, e2:int)
    requires 0 <= s1 <= e1 <= |s|;
    requires 0 <= s2 <= e2 <= e1 - s1;
    ensures  s[s1..e1][s2..e2] == s[s1+s2..s1+e2];
{
    var r1 := s[s1..e1];
    var r2 := r1[s2..e2];
    var r3 := s[s1+s2..s1+e2];
    assert |r2| == |r3|;
    forall i | 0 <= i < |r2|
        ensures r2[i] == r3[i];
    {
    }
}

lemma lemma_all_but_last_plus_last<T>(s:seq<T>)
    requires |s| > 0;
    ensures  all_but_last(s) + [last(s)] == s;
{}

lemma lemma_ConcatenationOf2Sequences<T>(s1:seq<T>, s2:seq<T>)
    ensures  forall i :: 0 <= i < |s1 + s2| ==> (s1 + s2)[i] == if i < |s1| then s1[i] else s2[i - |s1|];
{
}

lemma lemma_ConcatenationOf3Sequences<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>)
    ensures  forall i :: 0 <= i < |s1 + s2 + s3| ==>
                   (s1 + s2 + s3)[i] ==
                    if i < |s1| then s1[i]
                    else if i < |s1| + |s2| then s2[i - |s1|]
                    else s3[i - |s1| - |s2|];
{
}

lemma lemma_ConcatenationOf4Sequences<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>, s4:seq<T>)
    ensures  forall i :: 0 <= i < |s1 + s2 + s3 + s4| ==>
                   (s1 + s2 + s3 + s4)[i] ==
                    if i < |s1| then s1[i]
                    else if i < |s1| + |s2| then s2[i - |s1|]
                    else if i < |s1| + |s2| + |s3| then s3[i - |s1| - |s2|]
                    else s4[i - |s1| - |s2| - |s3|];
{
}

lemma lemma_ConcatenationOf5Sequences<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>, s4:seq<T>, s5:seq<T>)
    ensures  forall i :: 0 <= i < |s1 + s2 + s3 + s4 + s5| ==>
                   (s1 + s2 + s3 + s4 + s5)[i] ==
                    if i < |s1| then s1[i]
                    else if i < |s1| + |s2| then s2[i - |s1|]
                    else if i < |s1| + |s2| + |s3| then s3[i - |s1| - |s2|]
                    else if i < |s1| + |s2| + |s3| + |s4| then s4[i - |s1| - |s2| - |s3|]
                    else s5[i - |s1| - |s2| - |s3| - |s4|];
{
}

function {:opaque} MapSeqToSeq<T,U>(s:seq<T>, func:T->U) : seq<U>
    reads func.reads;
    requires forall i :: func.reads(i) == {};
    requires forall i :: 0 <= i < |s| ==> func.requires(s[i]);
    ensures |MapSeqToSeq(s, func)| == |s|;
    ensures forall i {:trigger func(s[i])} {:trigger MapSeqToSeq(s,func)[i]} :: 0 <= i < |s| ==> func(s[i]) == MapSeqToSeq(s,func)[i];
{
    if |s| == 0 then []
    else [func(s[0])] + MapSeqToSeq(s[1..], func)
}

function {:opaque} ConvertMapToSeq<T>(n:int, m:map<int, T>) : seq<T>
    requires n >= 0;
    requires forall i {:trigger i in m} :: 0 <= i < n ==> i in m;
    ensures  |ConvertMapToSeq(n, m)| == n;
    ensures  var s := ConvertMapToSeq(n, m);
             forall i {:trigger s[i]} :: 0 <= i < n ==> s[i] == m[i];
{
    if n == 0 then []
    else ConvertMapToSeq(n-1, m) + [m[n-1]]
}

function {:opaque} range(low:int, high:int) : seq<int>
    requires high >= low;
    ensures  |range(low, high)| == high - low;
    ensures  var s := range(low, high);
             forall i {:trigger s[i]} :: 0 <= i < high - low ==> s[i] == low + i;
    decreases high - low;
{
    if high == low then []
    else [low] + range(low+1, high)
}

lemma lemma_IfPairsOfSequencesHaveSameConcatenationAndFirstMatchesThenSecondMatches<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>, s4:seq<T>)
    requires s1 + s2 == s3 + s4;
    requires s1 == s3;
    ensures  s2 == s4;
{
}

lemma lemma_IfConcatenationIsPrefixAndFirstsMatchThenSecondIsPrefix<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>, s4:seq<T>)
    requires s1 + s2 <= s3 + s4;
    requires s1 == s3;
    ensures  s2 <= s4;
{
}

lemma lemma_IfTripletsOfSequencesHaveSameConcatenationAndFirstTwoMatchThenLastMatches<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>, s4:seq<T>, s5:seq<T>, s6:seq<T>)
    requires s1 + s2 + s3 == s4 + s5 + s6;
    requires s1 == s4;
    requires s2 == s5;
    ensures  s3 == s6;
{
}

lemma lemma_IfConcatenationIsPrefixAndFirstsAndSecondsMatchThenThirdIsPrefix<T>(s1:seq<T>, s2:seq<T>, s3:seq<T>, s4:seq<T>, s5:seq<T>, s6:seq<T>)
    requires s1 + s2 + s3 <= s4 + s5 + s6;
    requires s1 == s4;
    requires s2 == s5;
    ensures  s3 <= s6;
{
}

function IncrementSeq(s:seq<int>, amount:int) : seq<int>
    ensures var s' := IncrementSeq(s, amount);
            |s| == |s'| && forall i :: 0 <= i < |s'| ==> s'[i] == s[i] + amount;
{
    if s == [] then []
    else
        [s[0] + amount] + IncrementSeq(s[1..], amount)
}

}
