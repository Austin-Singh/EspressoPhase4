//(1)
//#7: non-static field 'a' cannot be referenced in a static context.
public class H {
    public int a;

    public static void main() {
	H.a = 9;
    }
}