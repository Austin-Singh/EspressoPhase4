//(1)
//#7: non-static method 'foo' cannot be referenced from a static context.
public class S {
    public void foo() { }

    public static void main() {
	foo();
    }
}