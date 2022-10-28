//(1)
//#6: Operator '!=' requires operands of the same type.
class test {
    public static void f() {}
    public static void main() {
	if (f() != null)
	    test = null;
    }
}