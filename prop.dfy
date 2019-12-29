module Prop {
    predicate shorterThan(sub: seq<int>, sequence: seq<int>)
    {
        |sub| < |sequence|
    }

    predicate strictlyIncreasing(a: array<nat>) 
    reads a
    {
        forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
    }

    predicate increasing(a: array<nat>) 
    reads a
    {
        forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
    }

    predicate subsetOf(x: array<int>, y: array<int>)
    reads x, y
    {
        multiset(y[..]) * multiset(x[..]) == multiset(x[..])
    }

    predicate boundedElements(x: array<nat>) 
    reads x
    {
        forall i :: 0 <= i < x.Length ==> 0 < x[i] <= x.Length
    }

    predicate uniformArray(x: array<nat>) 
    reads x
    {
        forall i, j :: 0 <= i < j < x.Length ==> x[i] == x[j]
    }
}