//(1)
//#10: non-static variable super cannot be referenced from a static context
public class GG {
    public int foo = 0;
}

public class FF extends GG {

    public static void foo() {
	super.foo = 9;
    }
}
