//(1)
//#6: Void type cannot be used here.
class test {
    public static void f() {}
    public static void main() {
	if (f() != f())
	    test = null;
    }
}
