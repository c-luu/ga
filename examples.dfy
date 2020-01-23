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

/*
    method Main()
    {
        assert count([]) == 0;
        assert count([true]) == 1;
        assert count([false]) == 0;
        assert count([true, false]) == 1;
        assert count([true, true]) == 2;
    }
*/
}

module BinarySearch {
    predicate sorted(a: seq<int>)
    {
        forall j,k :: 0 <= j < k < |a| ==> a[j] <= a[k]
    }

    predicate sorted'(a: array<int>)
    reads a
    {
        forall j,k :: 0 <= j < k < a.Length ==> a[j] <= a[k]
    }

    method search(a: seq<int>, key: int) returns (idx: int)
    requires sorted(a)
    ensures idx >= 0 ==> idx < |a| && a[idx] == key
    ensures idx < 0 ==> key !in a
    {
        var lo, hi := 0, |a|;

        while lo < hi
        decreases hi - lo
        invariant 0 <= lo <= hi <= |a|
        invariant key !in a[..lo] && key !in a[hi..]
        {
            var mid := (lo+hi)/2;
            if key < a[mid]
            {
                hi := mid;
            } else if a[mid] < key {
                lo := mid+1;
            } else {
                return mid;
            }
        }

        idx := -1;
    }

    lemma search'(a: array<int>, key: int) returns (idx: int)
    requires sorted'(a)
    ensures idx >= 0 ==> idx < a.Length && a[idx] == key
    ensures idx < 0 ==> key !in a[..]
    ensures key !in a[..] ==> idx == -1
    {
        var lo, hi := 0, a.Length;

        while lo < hi
        decreases hi - lo
        invariant 0 <= lo <= hi <= a.Length
        invariant key !in a[..lo] && key !in a[hi..]
        {
            var mid := (lo+hi)/2;
            if key < a[mid]
            {
                hi := mid;
            } else if a[mid] < key {
                lo := mid+1;
            } else {
                assert mid >= 0;
                assert mid < a.Length;
                assert a[mid] == key;
                return mid;
            }
        }

        return -1;
    }

/*
    method Main()
    {
        var a := new int[2];
        a[0] := 0;
        a[1] := 1;
        var r1 := search'(a, 0);
        assert a[0] == 0;
        assert  0 == r1; 

        var a1 := new int[2];
        a1[0] := 0;
        a1[1] := 1;
        var r2 := search'(a1, 3);
        assert  -1 == r2; 
    }
*/
}

