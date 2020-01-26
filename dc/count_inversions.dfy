include "../authoring/math.dfy"

import M = Math

/* 
 * An inversion is found if LHS, a, is greater
 * than RHS, b.
 */ 
function method inv(a: nat, b: nat): nat
{
    if M.methMax(a, b) == a then 1 else 0
}

method countInv(a: seq<nat>) returns (out: nat)
decreases a
requires |a| >= 0
{
    if |a| <= 1 {
        return 0;
    }
    var mid := if (|a|/2) % 2 == 0 then (|a|/2)-1 else |a|/2;
    var res1 := countInv(a[..mid]);
    var res2 := countInv(a[mid..]);
    var res3 := merge(a[..mid], a[mid..]); 
    out := res1 + res2 + res3;
}

method merge(a: seq<nat>, b: seq<nat>) returns (out: nat)
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

method Main()
{
    // Unordered sequence of numbers.
    var a1: seq<nat> := [6, 2, 1, 3];
    var a1l := a1[..2];
    var a1r := a1[2..];
    var res := countInv(a1);
    //print res;

    var a2: seq<nat> := [6, 2, 1];
    var res1 := countInv(a2);
    //print res1;

    var a3: seq<nat> := [];
    var res2 := countInv(a3);
    //print res2;

    var a4: seq<nat> := [0, 1];
    var res3 := countInv(a4);
    //print res3;
}