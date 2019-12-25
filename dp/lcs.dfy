function RecLCS(a: seq<char>, b: seq<char>): nat
//requires 0 < |a| == |b|
//requires 0 <= c <= |a| == |b|
requires 0 < |a| == |b|
decreases a, b
{
    if a[0] == b[0] && 1 < |a| == |b|
    then 1 + RecLCS(a[..|a|-1], b[..|b|-1])
    else 0
}

method computeLCS(a: seq<char>, b: seq<char>) returns (lcs: seq<char>) 
ensures multiset(lcs[..]) == multiset(a[..]) * multiset(b[..])
{}