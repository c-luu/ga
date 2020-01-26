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
}