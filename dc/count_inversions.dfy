include "../authoring/math.dfy"

import M = Math

/* 
 * An inversion is found if LHS, a, is greater
 * than RHS, b.
 */ 
function inv(a: nat, b: nat): nat
{
    if M.max(a, b) == a then 1 else 0
}

method Main()
{
    // Unordered sequence of numbers.
    var a1: seq<nat>;
}