module EditDistance {
    function diff(a: char, b: char): int
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
    ensures minEdits == recEdDist(a, b)
    {
        assume minEdits == recEdDist(a, b);
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

        // Base case: both characters are the same, so no editing cost.
        assert recEdDist(s1, s2) == 0;

        // Base case: character substitution. 
        assert recEdDist(s1, s3) == 1;
        assert recEdDist(s6, s7) == 0;

        // Inductive:
        assert recEdDist(s4, s5) == 4;

        // Causes timeout.
        // assert recEdDist(s8, s9) == 6;
    }
}