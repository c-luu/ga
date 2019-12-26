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

predicate leftPaddedDimMatrix(a: array2<char>, b: array2<nat>)
requires 0 < a.Length0 && 0 < a.Length1
reads a
{
    b.Length0 == a.Length0 && b.Length1 == a.Length1 
    && a[0, 0] == '\0' 
}

function recLCS(a: array2<char>, i: int, j: int): nat
reads a
decreases i, j
requires 0 <= i < a.Length0
requires 0 <= j < a.Length1
{
    if i == 0 || j == 0
        then 0
    else if a[i, j] != a[i, j]
        then if recLCS(a, i-1, j) > recLCS(a, i, j-1)
            then recLCS(a, i-1, j)
            else recLCS(a, i, j-1)
        else if a[i, j] == a[i, j]
            then if recLCS(a, i-1, j) > recLCS(a, i, j-1) && recLCS(a, i-1, j) > 1 + recLCS(a, i-1, j-1)
                then recLCS(a, i-1, j)
                else if recLCS(a, i, j-1) > recLCS(a, i-1, j) && recLCS(a, i, j-1) > 1 + recLCS(a, i-1, j-1)
                    then recLCS(a, i, j-1)
                    else 1 + recLCS(a, i-1, j-1)
            else 0
}

method dpLCS(s: array2<char>, lcsMatrix: array2<nat>) returns (lcsLen: nat)
requires 0 < lcsMatrix.Length0 == s.Length0 && 0 < lcsMatrix.Length1 == s.Length1
requires rowColInitializedMatrix(lcsMatrix)
requires leftPaddedDimMatrix(s, lcsMatrix)
ensures s.Length0-1 > 0 && s.Length1-1 > 0 ==> lcsLen == recLCS(s, s.Length0-1, s.Length1-1)
{
    var rowLen, colLen := lcsMatrix.Length0, lcsMatrix.Length1;
    var i, j := 1, 1;

    while i < rowLen
    decreases rowLen - i
    invariant 1 <= i <= rowLen
    {
        while j < colLen
        decreases colLen - j
        invariant 1 <= j <= colLen
        {
            j := j + 1;
        }

        i := i + 1;
    }

    assume s.Length0-1 > 0 && s.Length1-1 > 0 ==> lcsLen == recLCS(s, s.Length0-1, s.Length1-1);
}