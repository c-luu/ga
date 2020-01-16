// Input is a "corrupted" string where puncuations/ spaces are removed.
// S ::= corrupted input string.

/**
 * Axiom 1: A corrupted string may be reconstituted if
 * there's a range pair, or multiple non-overlapping pairs,
 * that are words and begin at index 0 and end before |S|.
 */

/** Base case 1: 
 *      Represents a substring that is a character that is also a word.
 *      forall i, j :: 0 <= i < j < |S|
 *      true if dict(S[i..j+1]), s.t. i+1 == j && j+1 == |S|
 */

 /**
  * Greedy approach:
  * Base case 1:
  *     forall i, j :: 0 <= i <= j < |S|
  *     G(S, i, j) ::=
  *     if i <= j < |S|:
  *         if dict(S[i..j+1]) 
  *            then if G(S,j+1,j+1)
  *                then true else false
  *         else if G(S,i,j+1) then true else false
  *     else:
  *         false
  */

predicate greedy_a1(S: string, i: nat, j: nat)
decreases |S| - i, |S| - j 
requires 0 <= i < j <= |S|
{
    if i<j<|S|-1 then
        if greedy_a1(S,i,j+1) then greedy_a1(S,j+1,j+2) else false 
    else if i<j<|S| then 
        (dict(S[i..j+1]) && greedy_a1(S,i,j+1)) 
    else dict(S[i..j])
}

// Limited dictionary function.
predicate dict(a: string)
{
    a in ["a", "as"]
}

method Main()
{
    assert dict("a");
    assert dict("s") == false;
    var a1 := "a";
    var a1' := a1[0..1];
    assert |a1[0..1]| == 1;
    assert a1[0..1] == "a";
    assert dict(a1);
    //var a2 := "aa";
    assert greedy_a1("a", 0, 1) == true;
    assert "as"[0..2] == "as";
    assert dict("as"[0..2]);
    assert greedy_a1("as", 0, 1) == true;
    assert "asa"[0..3] == "asa";
    assert greedy_a1("asa", 0, 1) == false;
    assert greedy_a1("aa", 0, 1) == true;
    //assert greedy_a1("asx", 0, 0) == false;
}