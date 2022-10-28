//(1)
//#9: field 'a' was declared 'private' and cannot be accessed outside its class.
public class W {
    private int a = 0;
}

public class X {
    public void foo(W w) {
	w.a = 9;
    }
}
