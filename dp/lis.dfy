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

method initLIS(x: array<nat>, val: nat) 
requires 0 < val <= x.Length
ensures uniformArray(x) 
ensures boundedElements(x)
modifies x
{
    forall i | 0 <= i < x.Length 
    {
        x[i] := val;
    }
}

/**
 * TODO: Make a post-condition (recursive) function
 * representing: L(i) == 1 + max_j { L(j) | a[j] < a[i] & j < i }
 * and use it below.
 */
method computeLIS(a: array<int>) returns (lisN: nat) 
requires a.Length > 0
ensures 0 <= lisN <= a.Length
ensures a == old(a)
{
    var n := a.Length;
    var lis := new nat[n];
    initLIS(lis, 1);

    var i, j := 0, 0;

    assert lis.Length == n;

    while i < n
    /**
     * TODO: We need a loop invariant
     * for each variable within the
     * loop if possible.
     * NOTE: invariants syntatically follow
     * the loop guard, but will be checked
     * before the loop guard.
     */
    invariant 0 <= j <= i <= n
    invariant boundedElements(lis)
    decreases n - i 
    {
        while j < i - 1 
        invariant 0 <= j <= i
        decreases i - j - 1 
        {
            if a[j] < a[i] && lis[i] < 1 + lis[j] {
                lis[i] := 1 + lis[j];
            }
            j := j + 1;
        }
        i := i + 1;
    }

    assert lis.Length <= n;

    var max := 0;
    var k := 1;

    while k < n
    invariant  0 <= max < k <= n
    decreases n - k 
    {
        if lis[k] > lis[max] {
            max := k;
        }
        k := k + 1;
    }

    assert max < lis.Length;
    assert max >= 0;

    lisN := lis[max];
    assert 0 <= lisN <= n;

    return lisN;
}
