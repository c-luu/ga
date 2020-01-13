include "../authoring/seq.dfy"

module EditDistance {
    import S = Seq

    function diff(a: char, b: char): nat
    {
        if a == b then 1 else 0
    }

    function recEdDist(a: string, b: string): nat
    requires |a| > 0 && |b| > 0
    {
        if a[|a|-1] == b[|b|-1] then 0 else 1
    }

    lemma recEdDist'(a: string, b: string, ai: nat, bi: nat) returns (dist: nat)
    requires |a| > 0 && |b| > 0
    requires 0 <= ai < |a|
    requires 0 <= bi < |b|
    {
        var res := [0, 0 ,0];
        res[0] := 1+recEdDist'(a, b, popChar(ai), bi);
        res[1] := 1+recEdDist'(a, b, ai, popChar(bi));
        res[2] := diff(a[ai], b[bi]) + recEdDist'(a, b, popChar(ai), popChar(bi));
    }

    function popChar(i: nat): nat
    requires i > 0
    {
        if i-1 < 0 then 0 else i-1 
    }

    method Main()
    {
        var s1 := "a";
        var s2 := "a";
        var s3 := "b";

        assert recEdDist(s1, s2) == 0;
        assert recEdDist(s1, s3) == 1;
    }
}