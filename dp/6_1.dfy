include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"

module SixOne {
    import M = Math
    import S = Seq
    import MX = MX

    function a1(a: seq<int>, i: nat): int
    decreases i
    requires 0<=i<|a|
    {
        if i==0 then M.max(0, a[i]) else
        M.max(0, a1(a,i-1)+a[i])
    }

    function method methA1(a: seq<int>, i: nat): int
    decreases i
    requires 0<=i<|a|
    {
        if i==0 then M.methMax(0, a[i]) else
        M.methMax(0, methA1(a,i-1)+a[i])
    }

    method Main()
    {
        // Base case.
        var a := [0];
        assert a1(a,|a|-1) == 0;

        var e := [0, 1];
        assert a1(e,|e|-1) == 1;

        var a' := [1, 0];
        assert a1(a',|a'|-1) == 1;

        var c' := [-1, 1];
        assert a1(c',|c'|-1) == 1;

        var c := [-1, 1, 2];
        assert a1(c,|c|-1) == 3;

        var b' := [5,-30,40,10];
        assert a1(b', |b'|-1) == 50;

        var b := [5,15,-30,10,-5,40,10];
        assert a1(b, |b|-1) == 55;

        var d := [-1, 1, 2, -2];
        //assert a1(d, |d|-1) == 3;
        var d_out := methA1(d, |d|-1);
        print d_out;
    }
}
