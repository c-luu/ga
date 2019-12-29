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
function recMaxContiguousSubseq(sequence: seq<int>, subSeq: seq<int>, i: int): int
decreases |sequence| - i
requires 0 <= i < |sequence|
{
    // Base case.
    if i == |sequence| then sequence[i-1] else
    if |sequence| == |subSeq| 
        then recMaxContiguousSubseq(sequence[i+1..], sequence[i+1..i+2], 0)
    else if Prop.seqSum(subSeq) > recMaxContiguousSubseq(sequence, sequence[..i+1], i+1)
        then Prop.seqSum(subSeq) else recMaxContiguousSubseq(sequence, sequence[..i+1], i+1)

    /*
    if i == 0 
        then 0
    else
    if s[i] > s[i] + recMaxContiguousSubseq(s, i-1)
        then s[i]
    else s[i] + recMaxContiguousSubseq(s, i-1)
    */
}

method maxContiguousSubseq(a: seq<int>) returns (subSeq: seq<int>, sum: int)
ensures Prop.shorterThan(subSeq, a)
ensures Prop.subsetOf(subSeq, a)
ensures Prop.increasing(subSeq) // or strictly increasing?
ensures maxSubseqSum(a, sum)
ensures sumOfEmptySubseq(subSeq, sum)
{
}