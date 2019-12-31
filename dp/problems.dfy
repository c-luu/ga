include "../prop.dfy"

// 6.1
// Base case(s):
predicate sumOfEmptySubseq(subSeq: seq<int>, sum: int) 
{
    |subSeq| == 0 ==> sum == 0
}

// Post-condition(s):
predicate maxSubseqSum(sequence: seq<int>, sum: int)
{
    // Do we need a total ordering such as this? Or less strict?
    forall i, j :: 0 <= i < j <= |sequence| ==> sum > Prop.seqSum(sequence[i..j])
}

// (TODO) Recurrence of contiguous subsequence of maxium sum:
// (TODO) Can probably do away with index i?
/*
function recMaxContiguousSubseq(sequence: seq<int>, subSeq: seq<int>, i: int): int
requires 0 <= i < |sequence|
{
    // Base case.
    if i == |sequence| then sequence[i-1] else
    if |sequence|-i == |subSeq| 
        then recMaxContiguousSubseq(sequence, sequence[i+1..i+1], i+1)
    else if Prop.seqSum(subSeq) > recMaxContiguousSubseq(sequence, sequence[..i+1], i+1)
        then Prop.seqSum(subSeq) else recMaxContiguousSubseq(sequence, sequence[..i+1], i+1)
}
*/

/**
----------------
5, 15, -30, 1, 0
----------------
5
5, 15
5, 15, -30
5, 15, -30, 1
5, 15, -30, 1, 0
15
15, -30
15, -30, 1
15, -30, 1, 0
-30
-30, 1
-30, 1, 0
1
1, 0
0
 */
function recMCS(s: seq<int>): int
requires 0 < |s|
{
    if |s| == 1 then Prop.seqSum(s[..]) else
    if Prop.seqSum(s[..1]) + recMCS(s[1..]) > recMCS(s[1..]) then Prop.seqSum(s[..1]) + recMCS(s[1..]) else recMCS(s[1..])
}

function method left(s: seq<int>): int
decreases s
requires |s| >= 1
{
    if |s| == 1 
        then Prop.seqSum'(s) 
    else if Prop.seqSum'(s) > Prop.seqSum'(s) + left(s[..|s|-1])
        then Prop.seqSum'(s)
    else Prop.seqSum'(s) + left(s[..|s|-1])
}

function method right(s: seq<int>): int
decreases s
requires |s| >= 1
{
    if |s| == 1 
        then Prop.seqSum'(s) 
    else if Prop.seqSum'(s) > Prop.seqSum'(s) + right(s[1..])
        then Prop.seqSum'(s)
    else Prop.seqSum'(s) + right(s[1..])
}

function method recMCS'(s: seq<int>): int
requires |s| > 1
{
    if left(s[..|s|-1]) > right(s[1..])
        then left(s[..|s|-1])
    else right(s[1..])
}

/*
method maxContiguousSubseq(a: seq<int>) returns (subSeq: seq<int>, sum: int)
ensures Prop.shorterThan(subSeq, a)
ensures Prop.subsetOf(subSeq, a)
ensures Prop.increasing(subSeq) // or strictly increasing?
ensures maxSubseqSum(a, sum)
ensures sumOfEmptySubseq(subSeq, sum)
{
}
*/

method Main()
{
    //assert recMCS'([5, 15, -30, 1, 0]) == 20;
    //assert Prop.seqSum([5, 15]) == 20;
    //assert Prop.seqSum([0]) == 0;
    //print Prop.seqSum'([5, 15, -30, 1, 0]);
    var x := [5, 15, -30, 1, 0];
    //assert Prop.seqSum(x) == -9;
    print recMCS'([5, 15, -30, 1, 0]);
}