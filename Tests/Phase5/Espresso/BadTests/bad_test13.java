//(1)
//#8: Method 'foo' declared non-static in superclass, cannot be reimplemented static.
public class Q {
    public void foo() { }
}

public class R extends Q {
    public static void foo() { }
}