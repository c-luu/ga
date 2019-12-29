include "../prop.dfy"

// 6.1
// Base case(s):
predicate sumOfEmptySubseq(subSeq: seq<int>, sum: int) 
{
    |subSeq| == 0 ==> sum == 0
}

predicate sumOfSingletonSeq(sequences: seq<int>, sum: int) 
{
    |sequences| == 1 ==> sum == 0
}

// (TODO) Recurrence of contiguous subsequence of maxium sum:
function recMaxContiguousSubseq(s: seq<int>, i: int): int
requires 0 <= i < |s|
{
    if i-1 < 0 
        then 0
    else
    if s[i] > s[i] + recMaxContiguousSubseq(s, i-1)
        then s[i]
    else s[i] + recMaxContiguousSubseq(s, i-1)
}

method maxContiguousSubseq(a: seq<int>) returns (subSeq: seq<int>, sum: int)
ensures Prop.shorterThan(subSeq, a)
ensures Prop.subsetOf(subSeq, a)
ensures Prop.increasing(subSeq) // or strictly increasing?
ensures sumOfEmptySubseq(subSeq, sum)
ensures sumOfSingletonSeq(a, sum)
{
}