// Output:
// Result: 89

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
	return a;
    }

}


class Main {
    public static void main() {
	A a = new A();
	Io.println(a.foo());
    }
}
