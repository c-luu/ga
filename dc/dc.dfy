include "../authoring/seq.dfy"

module MergeSort {
    import S = Seq

    method mergesort(a: seq<nat>) returns (out: seq<nat>)
    requires |a| > 0
    ensures |a| == 1 ==> out == a
    ensures S.increasing(out)
    decreases a
    {
        if |a| > 1 {
            var mid := |a|/2;
            var mergeRes := merge(a[..mid], a[mid..]);
            var res := mergesort(mergeRes);
        } else {
            return a;
        }
    }

    method merge(a: seq<nat>, b: seq<nat>) returns (out: seq<nat>)
    requires 0 < |a| && 0 < |b|
    ensures |a| == 1 ==> out == a
    ensures |b| == 1 ==> out == b
    ensures multiset(out) == multiset(a+b)
    ensures S.increasing(out)
    {
        if |a| == 1 {
            return a;
        }
         
        if |b| == 1 {
            return b;
        }

        if a[0] < b[0] {
            var res := merge(a[1..], b);
            var res' := [a[0]] + res;
            return res';
        } else {
            var res := merge(a, b[1..]);
            var res' := [b[0]] + res;
            return res';
        }
    }
}