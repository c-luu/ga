function RecLCS(a: seq<char>, b: seq<char>): nat
requires 0 < |a|
requires 0 < |b|
decreases a, b
{
    if a[|a|-1] == b[|b|-1] && 1 < |a| == |b|
    then 1 + RecLCS(a[..|a|-1], b[..|b|-1])
    else 0
}

method computeLCS(a: seq<char>, b: seq<char>) returns (lcs: seq<char>) 
ensures multiset(lcs[..]) == multiset(a[..]) * multiset(b[..])
{}