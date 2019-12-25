function RecLCS(a: seq<char>, b: seq<char>): nat
requires 0 < |a|
requires 0 < |b|
decreases a, b
{
    if a[|a|-1] == b[|b|-1] && 1 < |a| == |b|
    then 1 + RecLCS(a[..|a|-1], b[..|b|-1])
    else 0
}

function RecLCS2(a: array2<char>): nat
requires 0 < a.Length0
requires 0 < a.Length1
{
    if a.Length0 > 0 && a.Length1 == 0
    then 0
    else if a.Length0 == 0 && a.Length1 > 0
    then 0
    else if a[a.Length0-1][a.Length1-1] != a[a.Length0-1][a.Length1-1]
    then if RecLCS2(a[..a.Length0-1][a.Length1-1]) > RecLCS2(a[a.Length0-1][..a.Length1-1])
    then RecLCS2(a[..a.Length0-1][a.Length1-1])
    else RecLCS2(a[a.Length0-1][..a.Length1-1])
    else 0
}

method computeLCS(a: seq<char>, b: seq<char>) returns (lcs: seq<char>) 
ensures multiset(lcs[..]) == multiset(a[..]) * multiset(b[..])
{}