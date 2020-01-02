include "../prop.dfy"

function maxLIS(l: seq<nat>, a: seq<int>, val: int): int
decreases l, a
requires |l| == |a| > 0
{
    if |l| == 1 || |a| == 1 then l[|l|-1] else
    if l[|l|-1] == Prop.calcMax(l) && val >= a[|a|-1] then l[|l|-1]
    else maxLIS(l[..|l|-1], a[..|a|-1], val)
}

predicate computedLIS(l: seq<nat>, a: seq<int>)
requires |l| == |a| > 0
{
    forall i, j :: 0 <= j <= i-1 < |l|-1 && a[j] < a[i] 
        ==> l[i] == 1 + maxLIS(l[..j+1], a[..j+1], a[j])
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