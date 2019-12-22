predicate strictlyIncreasing(a: array<int>) 
reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
}

predicate subsetOf(x: array<int>, y: array<int>)
reads x, y
{
    multiset(y[..]) * multiset(x[..]) == multiset(x[..])
}

method computeLIS(a: array<int>) returns (lis: array<int>) 
ensures lis.Length <= a.Length
ensures strictlyIncreasing(lis)
ensures subsetOf(lis, a)
{
    return lis;
}