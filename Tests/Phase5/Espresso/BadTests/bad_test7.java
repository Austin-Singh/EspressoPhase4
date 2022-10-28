//(1)
//#7: non-static field 'a' cannot be referenced from a static context.
public class AA {
    public int a;

    public static void fpp(AA aa) {
	a = 9;
    }
}
