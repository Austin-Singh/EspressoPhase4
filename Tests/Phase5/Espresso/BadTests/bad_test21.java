//(1)
//#10: field 'a' was declared 'private' and cannot be accessed outside its class.
public class F {
    private int a;
}

public class G {
    public void foo() {
	F f = new F();
	f.a = 9;
    }
}
