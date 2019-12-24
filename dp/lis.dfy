predicate strictlyIncreasing(a: array<int>) 
reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] < a[j]
}

predicate increasing(a: array<int>) 
reads a
{
    forall i, j :: 0 <= i < j < a.Length ==> a[i] <= a[j]
}

predicate subsetOf(x: array<int>, y: array<int>)
reads x, y
{
    multiset(y[..]) * multiset(x[..]) == multiset(x[..])
}

method computeLIS(a: array<int>) returns (lisN: nat) 
requires a.Length > 0
ensures 0 <= lisN <= a.Length
{
    var n := a.Length;
    if n < 3 { return 1; }
    if n == 0 { return 0; }

    var lis := new nat[n];
    var i, j := 1, 1;

    while i < n 
    invariant 0 < j <= i <= n
    decreases n - i 
    {
        lis[i] := 1;

        while j < i - 1 
        invariant 0 < j <= i
        decreases i - j - 1 
        {
            if a[j] < a[i] && lis[i] < lis[j] {
                lis[i] := 1 + lis[j];
            }
            j := j + 1;
        }
        i := i + 1;
    }

    var max := 1;
    var k := 2;

    while k < n
    invariant 0 < max <= k <= n
    decreases n - k 
    {
        if lis[k] > lis[max] {
            max := k;
        }
        k := k + 1;
    }

    assert max > 0;
    assert max <= lis.Length;
   //assert increasing(lis);

    return lis[max];
}
