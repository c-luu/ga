include "../authoring/seq.dfy"

module SixSeventeen {
    import Seq = Seq

    class Obj {
        var weight: int;
        var value: int;
    }

    function totalWeight(s: seq<Obj>): int
    requires |s|>0
    decreases |s|
    reads s
    {
        if |s| == 1 then s[0].weight else
        s[0].weight + totalWeight(s[1..])
    }

    function method weightsLT(s: seq<Obj>, weight: int): seq<Obj>
    requires |s|>0
    decreases |s|
    reads s
    {
        if |s| == 1 then if s[0].weight <= weight then [s[0]] else []
        else if s[0].weight <= weight then [s[0]] + weightsLT(s[1..], weight)
        else weightsLT(s[1..], weight)
    }

    /**
     * The sum of weights in the optimum subset
     * is no more than the knapsack capacity.
     */
    predicate a1(totWeight: int, capacity: nat)
    {
        totWeight <= capacity
    }

    /**
     * This helps rule out trivial corner cases. 
     * Total weight is the sum of all object weights before algorithm begins.
     * See: https://pdfs.semanticscholar.org/8bc5/7f44bdd880a385b7c1338293ea4183f930ea.pdf
     */
     predicate a5(objs: seq<Obj>, totWeight: int, capacity: nat)
     reads objs
     {
         totWeight > capacity
         && forall o :: o in objs ==> o.weight <= capacity
     }

    /**
     * Optimum sum of values in the set.
     */
    predicate a2(maxVal: int, objs: seq<Obj>)
    {
        false
        //forall i :: i <= objs ==> maxVal >= 
    }

    /**
     * Knapsack type 2: with repetitions, i.e., unlimited
     * copies of each object.
     */
    method coinsDP(objs: seq<Obj>, s: seq<int>, capacity: nat) returns (maxVal: int)
    requires |s| == capacity+1 > 0 && s[0] == 0
    requires capacity > 1
    requires |objs| > 0
    requires a5(objs, totalWeight(objs), capacity)
    ensures a2(maxVal, objs)
    {
        var se := s;
        var i := 1;

        while i < capacity
        invariant capacity == capacity
        invariant |se| == capacity+1
        invariant 0 <= i <= capacity
        decreases capacity-i
        {
            var objslt := weightsLT(objs, i);
            assert |objslt| <= |objs|;
            assert multiset(objslt) <= multiset(objs);
            var j := 0;
            var subOpt := 0;

            while j < |objslt|-1
            invariant 0 <= j <= |objslt|-1
            invariant forall o :: o in objslt ==> o.weight <= i
            decreases |objslt|-j
            {
                var nw := i-objslt[j].weight;
                var nw' := i-objslt[j+1].weight;
                if se[nw] + objslt[j].value <= se[nw'] + objslt[j+1].value
                {
                    subOpt := se[nw']+objslt[j+1].value;
                } else { subOpt := se[nw]+objslt[j].value; }

                j := j+1;
            }

            assert |se| == capacity+1;
            assert i <= |se| == capacity+1;

            if j >= 1 {se := se[i := subOpt]; }
            j := 0;
            i := i+1;
        }
    }
}