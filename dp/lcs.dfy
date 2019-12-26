/**
 * References:
 * 1. https://en.wikipedia.org/wiki/Longest_common_subsequence_problem#Worked_example
 */

predicate validMatrix(a: array2<nat>)
reads a
{
    forall i, j :: ((0 <= i < a.Length0 && 0 <= j < a.Length1) 
                    && ((i == 0 && 0 <= j < a.Length1) || (j == 0 && 0 <= i < a.Length0))) 
                    ==> a[i, j] == 0 
}

function recLCS(a: seq<char>, b: seq<char>): nat
requires 0 < |a|
requires 0 < |b|
decreases a, b
{
    if a[|a|-1] == b[|b|-1] && 1 < |a| == |b|
    then 1 + recLCS(a[..|a|-1], b[..|b|-1])
    else 0
}

function recLCS2(a: array2<char>, i: int, j: int): nat
reads a
decreases i, j
requires 0 <= i < a.Length0
requires 0 <= j < a.Length1
{
    if i == 0 || j == 0
        then 0
    else if a[i, j] != a[i, j]
        then if recLCS2(a, i-1, j) > recLCS2(a, i, j-1)
            then recLCS2(a, i-1, j)
            else recLCS2(a, i, j-1)
        else if a[i, j] == a[i, j]
            then if recLCS2(a, i-1, j) > recLCS2(a, i, j-1) && recLCS2(a, i-1, j) > 1 + recLCS2(a, i-1, j-1)
                then recLCS2(a, i-1, j)
                else if recLCS2(a, i, j-1) > recLCS2(a, i-1, j) && recLCS2(a, i, j-1) > 1 + recLCS2(a, i-1, j-1)
                    then recLCS2(a, i, j-1)
                    else 1 + recLCS2(a, i-1, j-1)
            else 0
}

method dpLCS(s: array2<char>, lcsMatrix: array2<nat>) returns (lcsLen: nat)
requires 0 < lcsMatrix.Length0 && 0 < lcsMatrix.Length1
requires validMatrix(lcsMatrix)
ensures s.Length0-1 > 0 && s.Length1-1 > 0 ==> lcsLen == recLCS2(s, s.Length0-1, s.Length1-1)
{
    assume s.Length0-1 > 0 && s.Length1-1 > 0 ==> lcsLen == recLCS2(s, s.Length0-1, s.Length1-1);
}