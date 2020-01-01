module Prop {
    function calcMax(s: seq<int>): int
    decreases s
    requires |s| > 0
    {
        if |s| == 1 then s[|s|-1] else
        if s[|s|-1] > calcMax(s[..|s|-1])
            then s[|s|-1]
        else calcMax(s[..|s|-1])
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
}