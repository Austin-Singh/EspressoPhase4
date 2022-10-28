class test8 {
    public static int foo() {
	return 56;
    }
    public static void main(String args) {
        byte b= (byte)125546456d;
	int i=foo();
        b = (byte)(b + b);
        b++;;
        char c = (char)b;
	c++;
    }
}
