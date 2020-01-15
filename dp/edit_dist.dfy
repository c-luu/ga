include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"

module EditDistance {
    import Seq = Seq
    import MX = MX

    function diff(a: char, b: char): int
    {
        if a == b then 0 else 1
    }

    function method methDiff(a: char, b: char): int
    {
        if a == b then 0 else 1
    }

    function recEdDist(a: string, b: string): int
    requires |a| > 0 && |b| > 0
    {
        recEdDist'(a, b, 0, 0)
    }

    function recEdDist'(a: string, b: string, ai: nat, bi: nat): int
    requires 0 <= ai <= |a|
    requires 0 <= bi <= |b|
    decreases |a|-ai, |b|-bi
    {
        // Both strings are empty, nothing to edit.
        if ai == |a| && bi == |b| then 0 else

        /* If `a` is empty but not `b`, we need to
         * edit the remaining characters including
         * the character at index `bi`.
         */
        if ai == |a| then |b[bi..]| else
        if bi == |b| then |a[ai..]| else

        // There's gotta be a better way.
        if 1 + recEdDist'(a, b, ai+1, bi) < 1 + recEdDist'(a, b, ai, bi+1) 
            && 1 + recEdDist'(a, b, ai+1, bi) < diff(a[ai], b[bi]) + recEdDist'(a, b, ai+1, bi+1)
        then 1 + recEdDist'(a, b, ai+1, bi) else
        if 1 + recEdDist'(a, b, ai, bi+1) < 1 + recEdDist'(a, b, ai+1, bi) 
            && 1 + recEdDist'(a, b, ai, bi+1) < diff(a[ai], b[bi]) + recEdDist'(a, b, ai+1, bi+1)
        then 1 + recEdDist'(a, b, ai, bi+1) else
        diff(a[ai], b[bi]) + recEdDist'(a, b, ai+1, bi+1)
    }

    method edDist(a: string, b: string) returns (minEdits: nat)
    requires |a| > 0 && |b| > 0
    //ensures minEdits == recEdDist(a, b)
    {
        var a', b' := MX.dpStringMX(a, b);
        var m := new nat[|a'|, |b'|];
        var i, j := 1, 1;

        assert |a'| == |a| + 1;
        assert a'[0] == '\0';
        assert |b'| == |b| + 1;

        m[0,0] := 0;
        assert m[0, 0] == 0;

        while i < |a'|
        invariant 0 <= i <= |a'|
        decreases |a'|-i
        {
            m[i, 0] := i;
            i := i+1;
        }

        while j < |b'|
        invariant 0 <= j <= |b'|
        decreases |b'|-j
        {
            m[0, j] := j;
            j := j+1;
        }

        i, j := 1, 1;

        while i < |a'| 
        invariant 0 < i <= |a'|
        invariant j == 1
        decreases |a'|-i
        {
            assert forall a, b :: 0 <= a < |a'| && 0 <= b < |b'| ==> m[a,b] >=0;
            while j < |b'| 
            invariant 0 < i <= |a'|
            invariant 0 < j <= |b'|
            decreases |b'|-j
            {
                assert forall a, b :: 0 <= a < |a'| && 0 <= b < |b'| ==> m[a,b] >=0;
                var c1, c2, c3 := 1+m[i-1, j], 1+m[i, j-1], methDiff(a'[i],b'[j])+m[i-1,j-1];
                var resSeq := [c1, c2, c3];
                var localEdDist := Seq.minMeth(resSeq);
                m[i,j] := localEdDist;

                j := j+1;
            }

            i := i+1;
            j := 1;
        }

        minEdits := m[|a'|-1, |b'|-1];
        //assume minEdits == recEdDist(a, b);
    }

    method Main()
    {
        var s1 := "a";
        assert |s1| == 1;

        var s2 := "a";
        var s3 := "b";
        var s4 := "snowy";
        var s5 := "sunn";
        var s6 := "aa";
        var s7 := "aa";
        var s8 := "polynomial";
        var s9 := "exponential";
        var s10 := "\0snowy";
        var s11 := "\0sunny";

        // Base case: both characters are the same, so no editing cost.
        assert recEdDist(s1, s2) == 0;

        // Base case: character substitution. 
        assert recEdDist(s1, s3) == 1;
        assert recEdDist(s6, s7) == 0;

        // Inductive:
        assert recEdDist(s4, s5) == 4;

        // Causes timeout.
        // assert recEdDist(s8, s9) == 6;

        var res := edDist(s10, s11);
        print res;
        res := edDist(s8, s9);
        print '\n';
        print res;
    }
}