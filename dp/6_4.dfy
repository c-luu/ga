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

    function greedy_a1(S: string): multiset<string>
    decreases |S| - i, |S| - j 
    requires 0 < j <= |S|
    {
        greedy_a1'(S, 0, |S|)
    }

    function greedy_a1'(S: string, i: nat, j: nat): multiset<string>
    decreases |S| - i, |S| - j 
    requires 0 <= i < j <= |S|
    {
    }

    method Main()
    {
    }
}