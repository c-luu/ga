module Set {
    predicate greatestNum(a: set<int>, j: int) {
        forall i :: i in a ==> j >= i
    }

    predicate smallestNum(a: set<int>, j: int) {
        forall i :: i in a ==> j <= i
    }

    lemma sum(a: set<int>) returns (out: int)
    {
        var a' := a;
        out := 0;

        while a' != {}
        decreases a'
        {
            var t :| t in a';
            out := out + t;
            a' := a' - {t};
        }
    }

/*
    method Main()
    {
        var t1 := sum({ 0 });
        var t2 := sum({ 0, 1 });
        assert t1 == 0;
        assert t2 == 1;
    }
*/
}