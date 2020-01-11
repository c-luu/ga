module SkippingLemma {
    predicate one(a: array<int>) 
    reads a
    {
        forall i :: 0 <= i < a.Length ==> 0 <= a[i]
    }

    predicate two(a: array<int>)
    reads a
    {
        forall i :: 0 < i < a.Length ==> a[i-1] - 1 <= a[i]
    }

    method algo(a: array<int>) 
    requires one(a)
    requires two(a)
    {
        var idx := 0;
        while idx < a.Length
        decreases a.Length - idx
        invariant 0 <= idx 
        invariant forall k :: 0 <= k < idx && k < a.Length ==> a[k] != 0
        {
            if a[idx] == 0 { return; }
            skippingLemma(a, idx);
            idx := idx + a[idx];
        }

        idx := -1;
    }

    lemma skippingLemma(a: array<int>, j: int)
        requires one(a)
        requires two(a)
        requires 0 <= j < a.Length
        ensures forall i :: j <= i < j + a[j] && i < a.Length ==> a[i] != 0
    {
        var i := j;

        while i < j + a[j] && i < a.Length 
        decreases j + a[j] - i
        invariant i < a.Length ==> a[j] - (i-j) <= a[i]
        invariant forall k :: j <= k < i && k < a.Length ==> a[k] != 0
        {
            i := i+1;
        }
    }
}

module Distributive {
    // Counts # of `True`s.
    function count(a: seq<bool>): nat 
    decreases a
    {
        if |a| == 0 then 0 else 
        (if a[0] then 1 else 0) + count(a[1..])
    }

    predicate count'(a: seq<bool>, b: seq<bool>) {
        forall a, b {:induction a, b} :: count(a + b) == count(a) + count(b)
    }

    lemma distributiveLemma(a: seq<bool>, b: seq<bool>) 
    decreases a, b
    ensures count(a + b) == count(a) + count(b) 
    {
        if a == [] {
            assert a + b == b;
        } else {
            distributiveLemma(a[1..], b);
            assert a + b == [a[0]] + (a[1..] + b);
        }
    }

    method Main()
    {
        assert count([]) == 0;
        assert count([true]) == 1;
        assert count([false]) == 0;
        assert count([true, false]) == 1;
        assert count([true, true]) == 2;
    }
}

module Graphs {
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