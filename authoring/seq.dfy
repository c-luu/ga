// Authoring helpers for sequence data types.
module Seq {
    function calcMax(s: seq<int>): int
    requires |s| > 0
    {
        calcMax'(s, 0)
    }

    function calcMax'(s: seq<int>, idx: nat): int
    decreases |s| - idx
    requires 0 <= idx < |s|
    {
        if idx + 1 == |s| then s[idx] else
        if s[idx] > calcMax'(s, idx+1)
            then s[idx]
        else calcMax'(s, idx+1)
    }

    function calcMin(s: seq<int>): int
    requires |s| > 0
    {
        calcMin'(s, 0)
    }

    function calcMin'(s: seq<int>, idx: nat): int
    decreases |s| - idx
    requires 0 <= idx < |s|
    {
        if idx + 1 == |s| then s[idx] else
        if s[idx] < calcMin'(s, idx+1)
            then s[idx]
        else calcMin'(s, idx+1)
    }

    // https://raw.githubusercontent.com/dafny-lang/dafny/master/Test/tutorial/maximum.dfy
    method maxMeth(values: seq<int>) returns (max: int)
    requires values != []
    ensures max in values
    ensures forall i | 0 <= i < |values| :: values[i] <= max
    {
        max := values[0];
        var idx := 0;
        while (idx < |values|)
        decreases |values|-idx
        invariant max in values
        invariant idx <= |values|
        invariant forall j | 0 <= j < idx :: values[j] <= max
        {
            if (values[idx] > max) {
                max := values[idx];
            }
            idx := idx + 1;
        }
    }

    method minMeth(values: seq<int>) returns (min: int)
    requires values != []
    ensures min in values
    ensures forall i | 0 <= i < |values| :: values[i] >= min
    {
        min := values[0];
        var idx := 0;
        while (idx < |values|)
        decreases |values|-idx
        invariant min in values
        invariant idx <= |values|
        invariant forall j | 0 <= j < idx :: values[j] >= min
        {
            if (values[idx] <= min) {
                min := values[idx];
            }
            idx := idx + 1;
        }
    }

    function seqSum(sequence: seq<int>): int 
    decreases sequence
    requires |sequence| > 0
    {
        if |sequence| == 1 then sequence[|sequence|-1]
        else sequence[|sequence|-1] + seqSum(sequence[..|sequence|-1])
    }

    predicate shorterThan<T>(sub: seq<T>, sequence: seq<T>)
    {
        |sub| < |sequence|
    }

    predicate increasing(a: seq<int>) 
    {
        forall i, j :: 0 <= i < j < |a| ==> a[i] <= a[j]
    }

    predicate strictlyIncreasing(a: seq<int>) 
    {
        forall i, j :: 0 <= i < j < |a| ==> a[i] < a[j]
    }

    predicate subsetOf<T>(x: seq<T>, y: seq<T>)
    {
        multiset(y) * multiset(x) == multiset(x)
    }

    predicate boundedElements(x: seq<int>) 
    {
        forall i :: 0 <= i < |x| ==> 0 < x[i] <= |x|
    }

    predicate uniformArray<T>(x: seq<T>, val: T) 
    {
        forall i :: 0 <= i < |x| ==> x[i] == val
    }

/*
    method Main()
    {
        var s1 := [0, -1, 1, 2, -1];

        assert calcMin(s1) == -1;

        var r1 := maxMeth(s1);
        assert r1 == 2 == calcMax(s1);

        var r2 := minMeth(s1);
        assert r2 == -1 == calcMin(s1);
    }
    */
}
