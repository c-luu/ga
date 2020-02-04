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
    decreases a
    requires |a|>=0
    {
        if |a| == 0 then [] else
        if |a| == 1 then [a[0]] else 
        if a2([a[0]], a2(a, a[1..]))==[a[0]] then [a[0]]
        else if a2(a, a[1..]) == a then a else a1(a[1..])
    }

    function a2(a: seq<int>, b: seq<int>): seq<int>
    requires |a|>0 && |b|>0
    {
        if M.max(S.seqSum(a), S.seqSum(b)) == S.seqSum(a) then a else b
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

        var a'', a''' := [1, 0], [0, 0];
        assert a2(a'', a''') == a'';

        var a' := [1, 0];
        assert a1(a') == [a'[0]];
    }
}
