include "../prop.dfy"

// DPV
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

function left(s: seq<int>): int
requires |s| > 0
{
    if Prop.seqSum(s) > left'(s, 0, |s|)
        then Prop.seqSum(s)
    else left'(s, 0, |s|)
}

function left'(s: seq<int>, from: nat, to: nat): int
decreases |s| - from
requires 0 <= from < to <= |s|
{
    if from + 1 == to
        then s[from] 
    else if Prop.seqSum(s) > left'(s, from+1, to)
        then Prop.seqSum(s)
    else left'(s, from+1, to)
}

function right(s: seq<int>): int
decreases s
requires |s| >= 1
{
    if |s| == 1 
        then Prop.seqSum(s) 
    else if Prop.seqSum(s) > right(s[1..])
        then Prop.seqSum(s)
    else right(s[1..])
}

function recMCS(s: seq<int>): int
requires |s| > 1
{
    if left(s[..|s|-1]) > right(s[1..])
        then left(s[..|s|-1])
    else right(s[1..])
}

method dpMCS(a: seq<int>) returns (subSeq: seq<int>, sum: int)
requires |a| > 1
ensures Prop.shorterThan(subSeq, a)
ensures Prop.subsetOf(subSeq, a)
ensures Prop.increasing(subSeq) // or strictly increasing?
ensures maxSubseqSum(a, sum)
ensures sumOfEmptySubseq(subSeq, sum)
ensures sum == recMCS(a)
{
}

method Main()
{
    assert left([-1, 1, 1, -1]) == 0;
    assert recMCS([5, 15, -30, 10, -5, 40, 10]) == 55;
}