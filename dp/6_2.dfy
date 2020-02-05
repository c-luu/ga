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
    {
        a2(miles)
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

    // Min. function to serve as our recurrence.
    function a4(miles: seq<nat>, i: nat): nat
    requires 0 <= i < |miles|
    requires |miles|==1 ==> i==|miles|-1
    {
        if |miles|==0 then 0 else
        if |miles|==1 then miles[i] else 
        0
    }

/*
    method Main()
    {
    }
*/
}
