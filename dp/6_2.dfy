include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"
include "../util.dfy"

module SixTwo {
    import M = Math
    import S = Seq
    import MX = MX
    import U = Util

    /**
     * There is a hotel we can visit at each post i
     * of distance: miles[i].
     */
    predicate a1(miles: seq<nat>)
    requires |miles|>0 ==> miles[0] == 0
    requires a2(miles)
    {
        false
    }

    // Distances are strictly increasing.
    predicate a2(miles: seq<nat>)
    {
        forall i,j :: 0 <= i < j < |miles| 
            ==> miles[i] < miles[j]
    }

    // Cost function that we want to minimize.
    function a3(miles: nat): int
    {
        (200-miles)*(200-miles)
    }

/*
    method Main()
    {
    }
*/
}
