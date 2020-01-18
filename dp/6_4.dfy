include "../authoring/math.dfy"

module SixFour {
    import M = Math

    // Input is a "corrupted" string where puncuations/ spaces are removed.
    // S ::= corrupted input string.

    // Limited dictionary function.
    predicate dict(a: string)
    {
        a == "a" 
        || a == "as"
        || a == "the"
    }

    /**
     * An axiom stating if there exists
     * at least one word in string `S`,
     * the result evaluates to true.
     */
    predicate greedy_a1(S: string)
    requires |S| > 0
    {
        greedy_a1'(S, 0, 1)
    }

    predicate greedy_a1'(S: string, i: nat, j: nat)
    requires 0 <= i < j <= |S|
    decreases |S|-i , |S|-j
    {
        if dict(S[i..j]) then
            true
        else if j+1 <= |S| then
            greedy_a1'(S, i, j+1) 
        else if i+2 <= |S| then
            greedy_a1'(S, i+1, i+2) 
        else false
    }

    method Main()
    {
        // Positives.
        var s1, s2, s3, s4 := "a", "as", "aas", "aa";
        var s6 := "asa";
        var s7 := "sa";

        // Negatives.
        var s5 := "s";
        var s8 := "xx";

        assert greedy_a1(s1) == true;
        assert greedy_a1(s2) == true;
        assert greedy_a1(s3) == true;
        assert greedy_a1(s4) == true;
        assert greedy_a1(s6) == true;
        assert greedy_a1(s7) == true;

        // This is needed for some reason- might need a lemma?
        assert dict(s5) == false;
        assert greedy_a1(s5) == false;
        assert greedy_a1(s8) == false;
    }
}