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
requires 0 <= i <= j <= |S|
{
    if i <= j < |S|-1 then
        if dict(S[i..j+1]) then
        true else false
        /*
            if greedy_a1(S, j+1, j+1) then
                true else false
                */
                /*
        else if greedy_a1(S, i, j+1) then
            true else false
            */
    //else dict(S[i..j]) 
    else if j < |S| then dict(S[i..j]) 
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
    assert greedy_a1("a", 0, 0) == true;
}