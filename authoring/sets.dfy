module Set {
    predicate greatestNum(a: set<int>, j: int) {
        forall i :: i in a ==> j >= i
    }

    predicate smallestNum(a: set<int>, j: int) {
        forall i :: i in a ==> j <= i
    }
}