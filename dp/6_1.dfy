include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"

module SixOne {
    import M = Math
    import Seq = Seq
    import MX = MX

    /**
     * Axiom 1: Express the sub-problem
     * as a recurrence.
     */

    function a1(a: seq<nat>): seq<nat>
    requires |a|>0
    {
        if |a| == 1 then [a[0]] else 
        []
    }

    /**
     * Axiom 1': Express Axiom 1
     * in inductive form for Dafny.
     * 
     * TODO: Verify this if is needed.
     */

    method Main()
    {
        // Base case.
        var a := [0];
        assert a1(a) == a;
    }
}
