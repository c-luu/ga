/**
 * References:
 * 1. https://en.wikipedia.org/wiki/Longest_common_subsequence_problem#Worked_example
 */

predicate rowColInitializedMatrix(a: array2<nat>)
reads a
{
    forall i, j :: ((0 <= i < a.Length0 && 0 <= j < a.Length1) 
                    && ((i == 0 && 0 <= j < a.Length1) || (j == 0 && 0 <= i < a.Length0))) 
                    ==> a[i, j] == 0 
}

predicate leftPaddedDimMatrix(s1: seq<char>, s2: seq<char>, b: array2<nat>)
requires 0 < |s1| && 0 < |s2|
{
    b.Length0 == |s1| && b.Length1 == |s2|
    && s2[0] == s1[0] == '\0' 
}

function recLCS(s1: seq<char>, s2: seq<char>, i: int, j: int): nat
decreases i, j
requires 0 <= i < |s1|
requires 0 <= j < |s2|
{
    if i == 0 || j == 0
        then 0
    else if s1[i] != s2[j]
        then if recLCS(s1, s2, i-1, j) > recLCS(s1, s2, i, j-1)
            then recLCS(s1, s2, i-1, j)
            else recLCS(s1, s2, i, j-1)
        else if s1[i] == s2[j]
            then if recLCS(s1, s2, i-1, j) > recLCS(s1, s2, i, j-1) && recLCS(s1, s2, i-1, j) > 1 + recLCS(s1, s2, i-1, j-1)
                then recLCS(s1, s2, i-1, j)
                else if recLCS(s1, s2, i, j-1) > recLCS(s1, s2, i-1, j) && recLCS(s1, s2, i, j-1) > 1 + recLCS(s1, s2, i-1, j-1)
                    then recLCS(s1, s2, i, j-1)
                    else 1 + recLCS(s1, s2, i-1, j-1)
            else 0
}

method dpLCS(s1: seq<char>, s2: seq<char>, lcsMatrix: array2<nat>) returns (lcsLen: nat)
requires 0 < lcsMatrix.Length0 == |s1| && 0 < lcsMatrix.Length1 == |s2|
requires rowColInitializedMatrix(lcsMatrix)
requires leftPaddedDimMatrix(s1, s2, lcsMatrix)
ensures |s1|-1 > 0 && |s2|-1 > 0 ==> lcsLen == recLCS(s1, s2, |s1|-1, |s2|-1)
{
    var rowLen, colLen := lcsMatrix.Length0, lcsMatrix.Length1;
    var i, j := 1, 1;

    while i < rowLen
    decreases rowLen - i
    invariant 1 <= i <= rowLen
    invariant 1 <= j <= colLen
    {
        while j < colLen
        decreases colLen - j
        invariant 1 <= j <= colLen
        {
            j := j + 1;
        }

        i := i + 1;
    }

    assume |s1|-1 > 0 && |s2|-1 > 0 ==> lcsLen == recLCS(s1, s2, |s1|-1, |s2|-1);
}