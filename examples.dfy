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