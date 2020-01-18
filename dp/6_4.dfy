include "../authoring/math.dfy"

module SixFour {
    import M = Math

    // Input is a "corrupted" string where puncuations/ spaces are removed.
    // S ::= corrupted input string.

    // Limited dictionary function.
    predicate dict(a: string)
    {
        a in ["a", "as"]
    }

    predicate greedy_a1(S: string)
    {
        greedy_a1'(S, 0)
    }

    predicate greedy_a1'(S: string, i: nat)
    decreases |S| - i 
    {
        forall j {:induction j}:: 0 <= i < j <= |S| 
            ==> (dict(S[i..j]) || greedy_a1'(S, j))
    }

    method Main()
    {
        var s1, s2, s3, s4, s5 := "a", "as", "aas", "aa", "s";
        assert s1[0] == 'a';
        assert |s1| == 1;
        assert |s3| == 3;
        assert s5[0] == 's';
        assert dict(s5) == false;
        assert greedy_a1(s1) == true;
        assert greedy_a1(s2) == true;
        assert greedy_a1(s5) == false;
        assert greedy_a1(s3) == true;
        assert greedy_a1(s4) == true;
    }
}