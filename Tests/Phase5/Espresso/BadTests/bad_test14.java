//(1)
//#8: Method 'foo' declared static in superclass, cannot be reimplemented non-static.
public class O {
    public static void foo() { }
}

public class P extends O {
    public void foo() { }
}
