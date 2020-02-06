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

    predicate method methDict(a: string)
    {
        a == "a" 
        || a == "as"
        || a == "the"
    }

    // Needs to be <= O(n^2).
    method greedySixFour(a: string) returns (words: bool)
    requires |a|>0
    {
        if |a|==1 { return methDict(a); }
        var p := "\0" + a;

        var ar := new bool[|p|];
        ar[0] := true;
        var i := 1;

        while i < ar.Length 
        invariant 0<i<=|p|
        invariant 0<i<=ar.Length
        invariant |p|>2
        invariant ar.Length>2
        decreases ar.Length - i
        {
            if methDict([p[i]]) {
                ar[i] := true;
            } else {

            }
            i := i+1;
        }

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