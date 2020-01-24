include "../authoring/seq.dfy"

module MergeSort {
    import S = Seq

    // roughly: T(n) = 2T(n/2) + O(n) : a = 2, b = 2, d = 1. 
    // log_2(2) = 1, therefore T(n) = O(nlogn) via Master theorem.
    method recMergeSort(a: seq<nat>) returns (out: seq<nat>)
    requires |a| > 0
    ensures |a| == 1 ==> out == a
    ensures forall o :: o in out ==> o in a
    //ensures |a|>0 ==> S.increasing(out) 
    decreases a
    {
        if |a| > 1 {
            var mid := |a|/2;
            assert mid > 0;
            var left := recMergeSort(a[..mid]);  // T(n/2)
            var right := recMergeSort(a[mid..]); // + T(n/2)
            var recMergeRes := recMerge(left, right); // + O(n)
            out := recMergeRes;
        } else {
            return a;
        }
    }

    method recMerge(a: seq<nat>, b: seq<nat>) returns (out: seq<nat>)
    requires 0 <= |a| && 0 <= |b|
    ensures |a| == 0 && |b| >= 0 ==> out == b
    ensures |b| == 0 && |a| >= 0 ==> out == a
    ensures forall o :: o in out ==> o in a+b
    decreases a, b
    //ensures S.increasing(out)
    {
        if |a| == 0 && |b| >= 0 {
            return b;
        }
         
        if |b| == 0 && |a| >= 0 {
            return a;
        }

        if a[0] <= b[0] {
            var res := recMerge(a[1..], b);
            var res' := [a[0]] + res;
            return res';
        } else {
            var res := recMerge(a, b[1..]);
            var res' := [b[0]] + res;
            return res';
        }
    }

    method Main() {
        var a1 := [0, 2];
        var a2 := [1];
        var a3 := [0, 2, 1];
        var res1 := recMerge(a1, a2);
        var res2 := recMergeSort(a3);
        print res2;
    }
}