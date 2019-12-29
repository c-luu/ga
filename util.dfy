module Util {
    method printMatrix(a: array2<nat>) 
    {
        var v := 0;
        while (v < a.Length0)
        decreases a.Length0 - v
        {
            var y := 0;
            print "\n";
            while (y < a.Length1)
            decreases a.Length1 - y
            {
                print a[v, y];
                print "\t";
                y := y + 1;
            } 
            v := v + 1;
        } 
        print "\n";
    }
}