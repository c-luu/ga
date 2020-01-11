// Uncategorized proof helpers. 
module Prop {
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

// Graph theory related proof helpers.
module Graph {
    class Node {
        var next: seq<Node>;
    }

    predicate closed(graph: set<Node>) 
    reads graph
    {
        forall i :: i in graph ==> 
            forall k :: 0 <= k < |i.next| ==> i.next[k] in graph 
                                                && i.next[k] != i
    }
}