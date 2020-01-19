module KS {
    class Obj {
        var weight: int;
        var value: int;
    }

    lemma sums(objs: set<Obj>) returns (totWeight: int, totValue: int)
    {
        var objs' :set<Obj> := objs;
        while objs' != {}
        decreases objs'
        {
            var t :| t in objs';
            totWeight := totWeight + t.weight;
            totValue := totValue + t.value;
            objs' := objs' - {t};
        }
    }

    predicate a1(totWeight: int, capacity: nat)
    {
        totWeight <= capacity
    }

    lemma ks(objs: set<Obj>, capacity: nat) returns (so: set<Obj>, totWeight: int)
    ensures so <= objs
            && a1(totWeight, capacity)
    {}
}