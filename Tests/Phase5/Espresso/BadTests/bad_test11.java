//(1)
//#7: non-static method 'foo' cannot be referenced from a static context.
public class T {
    public void foo() { }
    
    public static void main() {
	T.foo();
    }
}
