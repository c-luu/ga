module Math {
    function min(a: int, b: int): int
    {
        if a < b then a else b
    }

    function method methMin(a: int, b: int): int
    {
        if a < b then a else b
    }

    function max(a: int, b: int): int
    {
        if a > b then a else b
    }
    
    function method methMax(a: int, b: int): int
    {
        if a > b then a else b
    }

    function method methFloorMid<T>(a: seq<T>): nat
    requires |a| > 1
    {
        if (|a|/2) % 2 == 0 then (|a|/2)-1 else |a|/2       
    }

    method methFloorMid'(l: nat, r: nat) returns (mid: nat)
    requires l <= r
    {
        return if ((l+r)/2) % 2 == 0 
                && ((l+r)/2)-1>0 
                then ((l+r)/2)-1 else (l+r)/2;
    }

    function diff(a: nat, b: nat): nat {
        if a-b < 0 then -1 * (a-b) else a-b
    }

    function method methDiff(a: nat, b: nat): nat {
        if a-b < 0 then -1 * (a-b) else a-b
    }
}