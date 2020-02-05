include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"
include "../util.dfy"

module SixOne {
    import M = Math
    import S = Seq
    import MX = MX
    import U = Util

    /**
     * Will fail assertion below because
     * the recurrence fails to implement
     * a recursive max-set operation as 
     * specified in the solutions.
     */
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

    method dp6_1(a: seq<int>) returns (out: int)
    requires |a|>0
    requires a[0] == 0
    {
        var arr := new int[|a|];
        assert arr.Length > 0;
        var i := 0;

        // O(n)
        while i < |a|
        decreases |a|-i
        {
            if i==0 {
                arr[i] := 0;
            } else {
                arr[i] := M.methMax(0, M.methMax(a[i], a[i]+arr[i-1]));
            }

            i := i+1;
        }

        // O(n)
        out := S.maxMethArr(arr);
    }

/*
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
        assert a1(d, |d|-1) == 3;

        var d' := [0,-1,1,2,-2];
        var d'_out := dp6_1(d');
        print d'_out;

        var b'' := [0,5,15,-30,10,-5,40,10];
        var b''_out := dp6_1(b'');
        print b''_out;
    }
    */
}
