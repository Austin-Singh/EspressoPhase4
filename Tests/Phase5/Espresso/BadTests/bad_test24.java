//(1)
//#8: Class 'B' cannot be extended because it has a private default constructor.
public class B {
    private B() {
    }
}

public class A extends B {
    private A() {
	super();
    }

    public static void main() {
	A a = new A();
    }
}