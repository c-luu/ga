include "../prop.dfy"

function maxLIS(l: seq<nat>, a: seq<int>, val: int): int
decreases l, a
requires |l| == |a| > 0
{
    if |l| == 1 || |a| == 1 then l[|l|-1] else
    if l[|l|-1] == Prop.calcMax(l) && val >= a[|a|-1] then l[|l|-1]
    else maxLIS(l[..|l|-1], a[..|a|-1], val)
}

predicate recLIS(l: seq<nat>, a: seq<int>)
requires |l| == |a| > 0
{
    forall i, j :: 1 <= j <= i-1 < |l|-1 && a[j] < a[i] 
        ==> l[i] == 1 + maxLIS(l[..j+1], a[..j+1], a[j])
}

method dpLIS()
{}