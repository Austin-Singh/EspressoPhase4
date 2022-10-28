// Output:
// Result: 16512

class Io {
    static public void print(byte b)  { }
    static public void print(short s) { }
    static public void print(char c)  { }
    static public void print(int i)   { }
    static public void print(long l)  { }
    static public void print(float f) { }
    static public void print(double d){ }
    static public void print(String s){ }
    static public void print(boolean b){ }
    static public void println(byte b) { }
    static public void println(short s){ }
    static public void println(char c) { }
    static public void println(int i)  { }
    static public void println(long l) { }
    static public void println(float f){ }
    static public void println(double d){ }
    static public void println(String s){ }
    static public void println(boolean b){ }

    static public int readInt() { }
    static public long readLong() { }
    static public float readFloat() { }
    static public double readDouble() { }
    static public String readString() { }
}

class A {
    int a;
    A() {
	a = 89;
    }
    int foo() {
	return -a;
    }
    void add(int a) {
        this.a = this.a + a;
    }
}


class Main {
    public static int b;
    public static void  main() {
	A a = new A();
	a.add(6);
	a.add(34);
	b=a.a;
	Io.println(a.foo()+a.a*b);
    }
}
