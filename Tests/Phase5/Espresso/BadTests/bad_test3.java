//(1)
//#6: non-static variable this cannot be referenced from a static context
public class HH  {
    public int foo;
    public static void foo() {
	this.foo = 9;
    }
}