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
     */
    function a1(a: seq<int>, i: nat): seq<int>
    decreases i
    requires 0<=i<|a|
    {
        if |a|==0 then [] else
        if i==0 then [a[i]] else 
        if a2([], a1(a,i-1)+[a[i]]) == [] then [] else
        a1(a,i-1)+[a[i]] 
    }

    function a1'(a: seq<int>, i: nat): int
    decreases i
    requires 0<=i<|a|
    {
        if i==0 then a[i] else
        if M.max(a[i], M.max(a1'(a,i-1), a1'(a,i-1)+a[i])) == a[i] then a[i] else
        if M.max(a1'(a,i-1), a1'(a,i-1)+a[i]) == a1'(a,i-1) then a1'(a,i-1) else
        a1'(a,i-1)+a[i] 
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
        /*
        var a := [0];
        assert a1'(a,|a|-1) == 0;

        var e := [0, 1];
        assert a1'(e,|e|-1) == 1;

        var a' := [1, 0];
        assert a1'(a',|a'|-1) == 1;

        var c' := [-1, 1];
        assert a1'(c',|c'|-1) == 1;

        var c := [-1, 1, 2];
        assert a1'(c,|c|-1) == 3;

        var d := [-1, 1, 2, -2];
        assert a1'(d, |d|-1) == 3;

        var b := [5,15,-30,10,-5,40,10];
        assert |b| == 7;
        assert S.seqSum(b[3..]) == 55;
        assert a1'(b, |b|-1) == 55;
        */
    }
}
