include "../authoring/math.dfy"
include "../authoring/seq.dfy"
include "../authoring/matrix.dfy"

module SixFour {
    import M = Math
    import Seq = Seq
    import MX = MX

    // Limited dictionary function.
    predicate method methDict(a: string)
    {
        /*a == "a" // Interesting case for non-greedy variant.
        ||*/ a == "as"
        || a == "the"
    }

    /**
     * Needs to be <= O(n^2), so be greedy unlike the proposed recurrence.
     * Due to the inner loop updating the outer loop counter, i,
     * to an unvisited character element, I suspect this O(n).
     */ 
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
                ar[i] := false;
                var j := i+1;

                while j < ar.Length
                invariant i <= j <= ar.Length
                invariant j<ar.Length ==> forall x :: i<=x<j ==> !ar[x]
                decreases ar.Length - j
                {
                    if methDict(p[i..j+1]) {
                        ar[j] := true;
                        i := j;
                        break;
                    } else { ar[j] := false; }
                    j := j+1;
                }
            }
            if i < ar.Length { i := i+1; }
            else { break; }
        }

        return ar[ar.Length-1];
    }

    method printWords(a: string, b: array<bool>) returns (words: seq<string>)
    requires b.Length == |a|+1
    requires b[0]
    {
        /**
         * This is straightforward to implement in O(n) but
         * we'll hand-wave here. Use the `true`'s in `b`
         * to backtrack the array to find word-breaks to
         * print out.
         */
    }

/*
    method Main()
    {
        // Positives.
        var s1, s4, s2 := "as", "asthe", "theas";

        var s1' := greedySixFour(s1);
        var s4' := greedySixFour(s4);
        var s2' := greedySixFour(s2);
        print s1';
        print s4';
        print s2';

        // Negatives.
        var s5 := "s";
        var s8 := "xx";
        var s5' := greedySixFour(s5);
        var s8' := greedySixFour(s8);
        print s5';
        print s8';
    }
*/
}