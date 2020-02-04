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
        if a2([a[0]], a2(a, a1(a[1..])))==[a[0]] then [a[0]] else
        if a2(a, a1(a[1..])) == a then a else a1(a[1..])
    }

    function a1'(a: seq<int>, i: nat): seq<int>
    decreases i
    requires 0<=i<|a|
    {
        if |a|==0 then [] else
        if i==0 then [a[i]] else 
        if a2([], a1'(a,i-1)+[a[i]]) == [] then [] else
        a1'(a,i-1)+[a[i]] 
    }

    function a1''(a: seq<int>, i: nat): int
    decreases i
    requires 0<=i<|a|
    {
        if |a|==0 then 0 else
        if i==0 then a[i] else 
        if a2([], a1'(a,i-1)+[a[i]]) == [] then 0 else
        S.seqSum(a1'(a,i-1))+a[i]
    }

    function a2(a: seq<int>, b: seq<int>): seq<int>
    requires |a|>=0 && |b|>=0
    {
        if |a|==0 && |b|>0 then a else
        if |b|==0 && |a|>0 then b else 
        if |b|==0 && |a|==0 then [] else
        if M.max(S.seqSum(a), S.seqSum(b)) == S.seqSum(a) then a else b
    }

    method Main()
    {
        // Base case.
        var a := [0];
        assert a1(a) == a;
        assert a1'(a, |a|-1) == a;

        var e := [0, 1];
        assert a1''(e, |e|-1) == 1;
        assert a1'(e, |e|-1) == e;
        assert a1(e) == e;

        var a' := [1, 0];
        assert a1'(a', |a'|-1) == a';
        assert a1(a) == a';

        var c' := [-1, 1];
        var c'_ans := [1];
        assert a1(c') == c'_ans;
        assert a1'(c', |c'|-1) == c'_ans;

        var c := [-1, 1, 2];
        var c_ans := [1, 2];
        assert a1(c) == c_ans;
        assert a1'(c, |c|-1) == c_ans;

        var d := [-1, 1, 2, -2];
        var d_ans := [1, 2];
        assert a1(d) == d_ans;


        var b := [5,15,-30,10,-5,40,10];
        var b_ans := [10,-5,40,10];
        assert a1(b) == b_ans;
    }
}
