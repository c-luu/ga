predicate strictlyIncreasing(a: array<int>) 
reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
}

method computeLIS(a: array<int>) returns (lis: array<int>) 
ensures lis.Length <= a.Length
ensures strictlyIncreasing(lis)
{
    return lis;
}