include "../authoring/seq.dfy"

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
    forall i, j :: 0 <= i < j <= |sequence| ==> sum > Seq.seqSum(sequence[i..j])
}

function left(s: seq<int>): int
decreases s
requires |s| >= 1
{
    if |s| == 1 
        then Seq.seqSum(s) 
    else if Seq.seqSum(s) > left(s[..|s|-1])
        then Seq.seqSum(s)
    else left(s[..|s|-1])
}

function right(s: seq<int>): int
decreases s
requires |s| >= 1
{
    if |s| == 1 
        then Seq.seqSum(s) 
    else if Seq.seqSum(s) > right(s[1..])
        then Seq.seqSum(s)
    else right(s[1..])
}

function recMCS(s: seq<int>): int
requires |s| > 1
{
    if left(s[..|s|-1]) > right(s[1..])
        then left(s[..|s|-1])
    else right(s[1..])
}

method maxContiguousSubseq(a: seq<int>) returns (subSeq: seq<int>, sum: int)
requires |a| > 1
ensures Seq.shorterThan(subSeq, a)
ensures Seq.subsetOf(subSeq, a)
ensures Seq.increasing(subSeq) // or strictly increasing?
ensures maxSubseqSum(a, sum)
ensures sumOfEmptySubseq(subSeq, sum)
ensures sum == recMCS(a)
{
}

method Main()
{
    assert recMCS([5, 15, -30, 10, -5, 40, 10]) == 55;
}