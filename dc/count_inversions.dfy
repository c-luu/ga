include "../authoring/math.dfy"

import M = Math

/* 
 * An inversion is found if LHS, a, is greater
 * than RHS, b.
 */ 
function method methInv(a: nat, b: nat): nat
{
    if M.methMax(a, b) == a then 1 else 0
}

function inv(a: nat, b: nat): nat
{
    if M.max(a, b) == a then 1 else 0
}

lemma merge(a: seq<nat>, b: seq<nat>) returns (out: nat)
decreases a, b
requires |a| >= 0 && |b| >= 0
{
    if |a| == 0 || |b| == 0 { out := 0; }
    else if inv(a[0], b[0]) == 1
        { 
            var res := merge(a, b[1..]);
            out := 1+res; 
        }
    else { out := merge(a[1..], b); }
}

method methMerge'(a: seq<nat>) returns (out: nat)
decreases a
requires |a| >= 0
{
    var mid := 0;
    if |a| > 1 {
        if |a| % 2 == 0 {
            mid := M.methMax((|a|/2)-1, (|a|/2)+1);
        } else { mid := |a|/2; }
        assert mid > 0;
        var res1 := methMerge'(a[..mid]);
        var res2 := methMerge'(a[mid..]);
        var res3 := methMerge(a[..mid], a[mid..]); 
        out := res1 + res2 + res3;
    } else { out := 0; }
}

method methMerge(a: seq<nat>, b: seq<nat>) returns (out: nat)
decreases a, b
requires |a| >= 0 && |b| >= 0
{
    if |a| == 0 || |b| == 0 { out := 0; }
    else if methInv(a[0], b[0]) == 1
        { 
            var res := methMerge(a, b[1..]);
            out := 1+res; 
        }
    else { out := methMerge(a[1..], b); }
}

method Main()
{
    // Unordered sequence of numbers.
    var a1: seq<nat> := [6, 2, 1, 3];
    var a1l := a1[..2];
    var a1r := a1[2..];
    var res := methMerge'(a1);
    print res;
}