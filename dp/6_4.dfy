include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"

module SixFour {
    import M = Math
    import Seq = Seq
    import MX = MX

    // Limited dictionary function.
    predicate dict(a: string)
    {
        a == "a" 
        || a == "as"
        || a == "the"
    }

    // Needs to be <= O(n^2).
    method greedySixFour(a: string) returns (words: bool)
    {
        return false;
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
    }
}