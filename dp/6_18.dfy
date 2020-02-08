include "../authoring/seq.dfy"

module SixEighteen {
    import Seq = Seq

    method coinsDP(v: nat, X: seq<nat>) returns (change: bool)
    ensures v == 0 ==> !change
    {
        if v == 0 { return false; }

        var a := new bool[v+1,|X|+1];

        // The next two lines are important for setting up the base case.
        a[0,0] := true;
        var i, j := 0, 1;

        while i < a.Length0
        decreases a.Length0-i
        {
            while j < a.Length1
            decreases a.Length1-j
            {
                a[i,j] := false;
                if (X[j-1] <= i && a[i-X[j-1], j-1]) || a[i, j-1]
                { a[i,j] := true; break; }

                j := j+1;
            }
            j := 1;
            i := i+1;
        }

        return a[a.Length0-1, a.Length1-1];
    }

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
}