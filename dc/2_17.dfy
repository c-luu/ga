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
decreases a
requires |a| >= 0
{
    if |a| <= 1 {
        return 0;
    }
    var mid := M.methFloorMid(a);
    var res1 := recFxdPnts(a, start, mid);
    var res2 := recFxdPnts(a, mid, 2*mid);
    var res3 := merge(a[..mid], a[mid..]); 
    out := res1 + res2 + res3;
}

method Main()
{
    // Unordered sequence of numbers.
    var a1: seq<nat> := [6, 2, 1, 3];
}