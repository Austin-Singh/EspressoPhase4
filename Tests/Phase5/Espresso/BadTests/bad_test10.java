//(1)
//#10: foo( ) has private access in 'U'.
public class U {
    private void foo() { }
}

public class V {
    public static void main() {
	U u = new U();
	u.foo();
    }
}
