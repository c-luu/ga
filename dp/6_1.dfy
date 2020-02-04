include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"

module SixOne {
    import M = Math
    import S = Seq
    import MX = MX

    /**
     * Axiom 1: Express the sub-problem
     * as a recurrence.
     * This may need to be adjusted to form T(n, a), where
     * n is a[|a|-1].
     */
    function a1(a: seq<int>): seq<int>
    requires |a|>=0
    {
        if |a| == 0 then [] else
        if |a| == 1 then [a[0]] else 
        []
    }

    /**
     * Axiom 1': Express Axiom 1
     * in inductive form for Dafny, if needed.
     */

    method Main()
    {
        // Base case.
        var a := [0];
        assert a1(a) == a;

        var a' := [1, 0];
        assert a1(a') == a'[0];
    }
}
