include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"

module SixEight {
    import M = Math
    import Seq = Seq
    import MX = MX

    // O(|a||b|)
    method lcs(a: string, b: string) returns (k: nat)
    requires |a|>0 && |b|>0
    {
        var a', b' := MX.dpStringMX(a, b);
        var m := new nat[|a'|, |b'|];
        var i, j := 0, 0;

        while i < |a'|
        decreases |a'|-i
        {
            m[i, 0] := 0;
            i := i+1;
        }

        while j < |b'|
        decreases |b'|-j
        {
            m[0, j] := 0;
            j := j+1;
        }

        i, j := 1, 1;
        k := 0;

        while i < |a'|
        decreases |a'|-i
        {
            while j < |b'|
            decreases |b'|-j
            {
                if a'[i] == b'[j]
                {
                    m[i,j] := 1 + m[i-1,j-1];
                    k := M.methMax(m[i, j], k);
                } else {
                    m[i,j] := 0;
                }

                j := j+1;
            }
            j := 1;
            i := i+1;
        }

        return k;
    }

/*
    method Main()
    {
        var a1 := "cab";
        var a2 := "cacab";
        var ans1 := lcs(a1, a2);
        print ans1;
        var a3 := "azcabz";
        var a4 := "safcab";
        var ans2 := lcs(a3, a4);
        print ans2;
    }
*/
}