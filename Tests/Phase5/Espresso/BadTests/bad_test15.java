//(1)
//#8: Method 'foo' was implemented as final in super class, cannot be reimplemented.
public class M {
    public final void foo() { }
}

public class N extends M {
    public void foo() { }
}
