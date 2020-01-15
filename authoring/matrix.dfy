module MX {
    // Returns null-prefixed strings for a 2-d matrix.
    method dpStringMX(a: string, b: string) 
    returns (a': string, b': string)
    requires |a| > 0 && |b| > 0
    ensures |a'| == |a|+1
    ensures |b'| == |b|+1
    ensures a'[0] == '\0'
    ensures b'[0] == '\0'
    {
        a' := "\0" + a;
        b' := "\0" + b;
    }
}
