include "../authoring/seq.dfy"

module SixSeventeen {
    import Seq = Seq

    /**
     * O(v|X|).
     * This implementation was a little tricky. The interesting note
     * is the semantics of what data a[i] represents. In this case,
     * it holds true if 0 <= i < v and i >= X[j], for some j, and 
     * a[i-1] also exhibits this property.
     *
     * The lemma seems to be that if each value, i, up to the target
     * value, v, can be made change for at least `one` domination, 
     * and so does i-1, then the final value v can as well.
     */
    method coinsDP(v: nat, X: seq<nat>) returns (change: bool)
    ensures v == 0 ==> !change
    {
        if v == 0 { return false; }

        var a := new bool[v+1];
        a[0] := true;
        var i, j := 1, 0;

        while i < a.Length
        decreases a.Length-i
        {
            a[i] := false;
            while j < |X|
            decreases |X|-j
            {
                // https://huadonghu.com/archives/en/dpv-6-17-coins-of-denominations/
                if X[j] <= i && a[i-X[j]] { a[i] := true; break; }
                j := j+1;
            }
            j := 0;
            i := i+1;
        }
        return a[a.Length-1];
    }

    method Main()
    {
        var x := [4, 2];
        var v := 5;
        var v' := 6;
        var ans := coinsDP(v, x);
        var ans' := coinsDP(v', x);
        print ans;
        print ans';
    }
}