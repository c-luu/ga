include "../prop.dfy"

// https://www8.cs.umu.se/kurser/TDBA77/VT06/algorithms/BOOK/BOOK2/NODE47.HTM
predicate computedLIS(l: seq<nat>, a: seq<int>)
requires |l| == |a| > 0
{
    forall i, j {:induction j} :: 0 <= j <= i-1 < i < |l| ==>
    (a[j] < a[i] ==> l[i] == 1 + computedLIS'(l, a, a[i], 0, i))
}

function computedLIS'(l: seq<nat>, a: seq<int>, val: int, start: nat, end: nat): int
decreases |l| - start
requires 0 <= start <= end < |l| == |a|
{
    if end == 0 then 1 else
    if start == end then l[start] else
    if l[start] == Prop.calcMax(l) && val >= a[start] then l[start]
    else computedLIS'(l, a, val, start+1, end)
}

predicate recLIS(lisRes: int, l: seq<nat>, a: seq<int>)
requires |l| == |a| > 0
requires computedLIS(l, a)
{
    lisRes == Prop.calcMax(l)
}

/**
 * All elements to the right of `i` in L
 * should be initialized, and nothing more.
 */
predicate rhsLISInvariant(i: nat, l: seq<nat>)
{
    forall k :: i < k < |l| ==> l[k] == 1
}

/**
 * There's at least one element to the left of `i`
 * that is the LIS in L. If all of them are the same,
 * return any one of them?
 */
predicate lhsLISInvariant(l: seq<nat>, a: seq<int>)
requires |l| == |a| > 1
requires computedLIS(l, a)
{
    exists k: nat :: k in l && recLIS(k, l, a)
}

method dpLIS(l: seq<nat>, a: seq<int>) returns (lis: nat)
requires |l| == |a| > 0
requires Prop.uniformArray(l, 1)

ensures computedLIS(l,a)
ensures recLIS(lis, l, a)
{
    var i, j := 0, 0;

    while i < |a|
    decreases |a|-i
    invariant i <= |a|
    invariant j == 0
    invariant rhsLISInvariant(i, l)
    invariant lhsLISInvariant(l[..i], a[..i])
    {
        while j < i-1
        decreases i - j - 1
        invariant j <= i
        {
            j := j+1;
        }

        j := 0;
        i := i+1;
    }

    assume computedLIS(l, a) && recLIS(lis, l, a);
}

method Main()
{
    var a := [5, 7, 4, -3, 9, 1, 10, 4, 5, 8, 9, 3];
    var l := [1, 2, 1,  1, 3, 2, 4,  3, 4, 5, 6, 3];
    
    assert computedLIS(l, a);
    assert recLIS(6, l, a);
}