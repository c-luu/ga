include "../authoring/seq.dfy"

module SixNineteen {
    import Seq = Seq

    method coinsDP(v: nat, k: nat, X: seq<nat>) returns (change: bool)
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
            print a[i];
            j := 0;
            i := i+1;
        }

        return a[a.Length-1];
    }

/*
    method Main()
    {
        var x := [4, 2];
        var v := 8;
        var v' := 6;
        var v'' := 2;
        var ans := coinsDP(v, x);
        var ans' := coinsDP(v', x);
        var ans'' := coinsDP(v'', x);
        print ans;
        print ans';
        print ans'';
    }
*/
}