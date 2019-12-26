/**
 * References:
 * 1. https://en.wikipedia.org/wiki/Longest_common_subsequence_problem#Worked_example
 */
 
function RecLCS(a: seq<char>, b: seq<char>): nat
requires 0 < |a|
requires 0 < |b|
decreases a, b
{
    if a[|a|-1] == b[|b|-1] && 1 < |a| == |b|
    then 1 + RecLCS(a[..|a|-1], b[..|b|-1])
    else 0
}

function RecLCS2(a: array2<char>, i: int, j: int): nat
reads a
decreases i, j
requires -1 <= i < a.Length0
requires -1 <= j < a.Length1
{
    if i < 0 || j < 0
        then 0
    else if a[i, j] != a[i, j]
        then if RecLCS2(a, i-1, j) > RecLCS2(a, i, j-1)
            then RecLCS2(a, i-1, j)
            else RecLCS2(a, i, j-1)
        else if a[i, j] == a[i, j]
            then if RecLCS2(a, i-1, j) > RecLCS2(a, i, j-1) && RecLCS2(a, i-1, j) > 1 + RecLCS2(a, i-1, j-1)
                then RecLCS2(a, i-1, j)
                else if RecLCS2(a, i, j-1) > RecLCS2(a, i-1, j) && RecLCS2(a, i, j-1) > 1 + RecLCS2(a, i-1, j-1)
                    then RecLCS2(a, i, j-1)
                    else 1 + RecLCS2(a, i-1, j-1)
            else 0
}