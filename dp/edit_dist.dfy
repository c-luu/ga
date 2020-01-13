include "../authoring/seq.dfy"

module EditDistance {
    import Seq = Seq

    function popChar(i: int): int
    requires i >= 0
    {
        if i-1 < 0 then 0 else i-1 
    }

    function diff(a: char, b: char): int
    {
        if a == b then 0 else 1
    }

    function recEdDist(a: string, b: string): int
    requires |a| > 0 && |b| > 0
    {
        0
    }

    function case1(a: string, b: string, ai: nat, bi: nat): int
    requires 0 < ai+1 < |a|
    requires 0 < bi+1 < |b|
    decreases |a|- ai
    {
        1 + recEdDist'(a, b, ai+1, bi)
    }

    function case2(a: string, b: string, ai: nat, bi: nat): int
    requires 0 < ai+1 < |a|
    requires 0 < bi+1 < |b|
    decreases |b| - bi
    {
        1 + recEdDist'(a, b, ai, bi+1)
    }

    function case3(a: string, b: string, ai: nat, bi: nat): int
    requires 0 < ai+1 < |a|
    requires 0 < bi+1 < |b|
    decreases |a|- ai, |b| - bi
    {
        diff(a[ai], b[bi]) + recEdDist'(a, b, ai+1, bi+1)
    }

    function recEdDist'(a: string, b: string, ai: nat, bi: nat): int
    requires 0 <= ai < |a|
    requires 0 <= bi < |b|
    decreases |a|- ai, |b| - bi
    {
        // Both strings are empty, nothing to edit.
        if ai+1 == |a| && bi+1 == |b| then 0 else

        /* If `a` is empty but not `b`, we need to
         * edit the remaining characters including
         * the character at index `bi`.
         */
        if ai+1 == |a| then |b[bi..]| else
        if bi+1 == |b| then |a[ai..]| else
        if case1(a, b, ai, bi) < case2(a, b, ai, bi) 
            && case1(a, b, ai, bi) < case3(a, b, ai, bi)
        then case1(a, b, ai, bi) else
        if case2(a, b, ai, bi) < case1(a, b, ai, bi) 
            && case2(a, b, ai, bi) < case3(a, b, ai, bi)
        then case2(a, b, ai, bi) else
        case3(a, b, ai, bi)
    }


    lemma editDist(a: string, b: string, ai: int, bi: int) returns (dist: int)
    requires |a| > 0 && |b| > 0
    requires 0 <= ai < |a|
    requires 0 <= bi < |b|
    decreases ai, bi
    {
        var case1, case2, case3 :int;

        if ai-1 < 0 {
            case1 := 0;
        } else {
            case1 := editDist(a, b, ai-1, bi);
            case1 := 1 + case1;
        }

        if bi-1 < 0 {
            case2 := 0;
        } else {
            case2 := editDist(a, b, ai, bi-1);
            case2 := 1 + case2;
        }

        if ai-1 < 0 || bi-1 < 0 {
            case3 := 0;
        } else {
            case3 :=  editDist(a, b, ai-1, bi-1);
            case3 := diff(a[ai], b[bi]) + case3;
        }


        var res :seq<int> := [case1, case2 , case3];
        dist := Seq.calcMin(res);
    }


    method Main()
    {
        var s1 := "a";
        var s2 := "a";
        var s3 := "b";

        // Base case: both characters are the same, so no editing cost.
        assert recEdDist(s1, s2) == 0;

        // Base case: character substitution. 
        assert recEdDist(s1, s3) == 1;
    }
}