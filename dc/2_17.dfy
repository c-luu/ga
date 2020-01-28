include "../authoring/math.dfy"

import M = Math

/**
 * Checks if the element is equal to it's index.
 */
predicate baseCase1(a: int, idx: nat)
{
    a == idx
}

predicate axiom1(a: seq<int>)
{
    forall i :: 0 <= i < |a| && a[i]==i
}

method recFxdPnts(a: seq<nat>, start: nat, end: nat) returns (out: nat)
requires |a| >= 1 && end >= start 
decreases end - start
{
    if start <= end {
        if |a| > 1 {
            var mid := M.methFloorMid(a);
            if mid == a[mid] { return 1; }
            if mid > a[mid] && mid+1 <= end {
                var res := recFxdPnts(a, mid+1, end);
                return res;
            }
            if start <= mid {
                var res := recFxdPnts(a, start, mid);
                return res;
            }
        } else { return if a[0] == end then 1 else 0; }
    }

    else { return 0; }
}

method Main()
{
    // Unordered sequence of numbers.
    var a1: seq<nat> := [6, 2, 1, 3];
    var res := recFxdPnts(a1, 0, |a1|);
    print res;
}