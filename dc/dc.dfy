include "../authoring/seq.dfy"

module MergeSort {
    import S = Seq

    method mergesort(a: seq<nat>) returns (out: seq<nat>)
    requires |a| > 0
    ensures |a| == 1 ==> out == a
    ensures S.increasing(out)
    ensures |a| == |out|
    decreases a
    {
        if |a| > 1 {
            var mid := |a|/2;
            assert mid > 0;
            var left := mergesort(a[..mid]); 
            var right := mergesort(a[mid..]);
            var mergeRes := merge(left, right);
            out := mergeRes;
        } else {
            return a;
        }
    }

    method merge(a: seq<nat>, b: seq<nat>) returns (out: seq<nat>)
    requires 0 <= |a| && 0 <= |b|
    ensures |a| == 0 ==> out == b
    ensures |b| == 0 ==> out == a
    ensures S.increasing(out)
    {
        if |a| == 0 {
            return b;
        }
         
        if |b| == 0 {
            return a;
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