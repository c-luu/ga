function RecLCS(a: seq<char>, b: seq<char>): nat
requires 0 < |a|
requires 0 < |b|
decreases a, b
{
    if a[|a|-1] == b[|b|-1] && 1 < |a| == |b|
    then 1 + RecLCS(a[..|a|-1], b[..|b|-1])
    else 0
}

function RecLCS2(a: array2<char>, i: nat, j: nat): nat
reads a
decreases i, j
requires 0 <= i < a.Length0
requires 0 <= j < a.Length1
{
    if i > 0 && j == 0
    then 0
    else if i == 0 && j > 0
    then 0
    else if a[i, j] != a[i, j]
        then if RecLCS2(a, i-1, j) > RecLCS2(a, i, j-1)
        then RecLCS2(a, i-1, j)
        else RecLCS2(a, i, j-1)
    else 0
}

method computeLCS(a: seq<char>, b: seq<char>) returns (lcs: seq<char>) 
ensures multiset(lcs[..]) == multiset(a[..]) * multiset(b[..])
{}