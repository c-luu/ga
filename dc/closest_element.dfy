include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../util.dfy"

import M = Math
import U = Util
import S = Seq

// Assume inputs are sorted initially.
method closestElem(a: seq<nat>, b: seq<nat>, out: array<nat>)
modifies out
requires |a| == |b| > 0
requires S.strictlyIncreasing(b)
requires out.Length == |a|
requires |a| > 0
{
    if |a| == 1 { out[0] := b[0]; }
    var i := 0;

    while i < |a|
    decreases |a|-i
    {
        var res := merge''(a[i], b);
        out[i] := res;
        i := i+1;
    }
}

method merge''(c: nat, b: seq<nat>) returns (out: nat)
decreases b
requires |b| > 0
{
    if |b| == 1 {
        return b[0];
    }

    var mid := M.methFloorMid(b);
    var l := b[..mid];
    var r := b[mid..];

    if M.methDiff(c, l[0]) <= M.methDiff(c, r[0]) {
        if |l| > 1 { 
            var res := merge''(c, l[1..]);
            out := if M.methDiff(c, l[0]) <= M.methDiff(c, res)
                   then l[0] else res;
        }
        else { out := l[0]; }
        
    } 
    else { 
        if |r| > 1 { 
            var res := merge''(c, r[1..]); 
            out := if M.methDiff(c, r[0]) <= M.methDiff(c, res)
                   then r[0] else res;
        }
        else { out := r[0]; }
    }
}

method Main()
{
    /**
     * https://en.wikipedia.org/wiki/Closest_pair_of_points_problem#Planar_case
     * Inputs a, b are distinct sequences.
     * Output c is a multi-subset of b.
     */
    var a := [6, 1, 12];
    var b := [1, 3, 10];
    var c := [3, 1, 10];
    var c_out := new nat[|a|];
    closestElem(a, b, c_out);
    U.printArray(c_out);

    var a' := [1, 6, 12];
    var b' := [1, 3, 10];
    var c' := [1, 3, 10];
    var c'_out := new nat[|a'|];
    closestElem(a', b', c'_out);
    U.printArray(c'_out);
    
    var a1 := [6, 1, 12];
    var b1 := [0, 1, 8];
    var c1 := [8, 1, 8];
    var c1'_out := new nat[|a1|];
    closestElem(a1, b1, c1'_out);
    U.printArray(c1'_out);

    var a2 := [0];
    var b2 := [1];
    var c2 := [1];
    var c2' := new nat[|a2|];
    closestElem(a2, b2, c2');
    U.printArray(c2');
}