// Output:
// 8
// 8
// Result: 0
class Io {
    static public void print(byte b) { }
    static public void print(short s) { }
    static public void print(char c) { }
    static public void print(int i) { }
    static public void print(long l) { }
    static public void print(float f) { }
    static public void print(double d){ }
    static public void print(String s){ }
    static public void print(boolean b){ }
    static public void println(byte b) { }
    static public void println(short s){ }
    static public void println(char c) { }
    static public void println(int i) { }
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
    B b;
    A a;
    int value;
}

class B {
    A a;
    B b;
    int value;
}

class Main {
    int main() {
	A a = new A();
	B b = new B();

	a.b = b.b = b;
	b.a = a.a = a;

	a.b.a.b.a.b = b.a.b.a.b.a.b.a.b;
	a.b.a.b.a.value = 8;
	b.a.b.a.b.value = a.b.a.b.a.b.a.b.a.value;
	Io.println(a.value);
	Io.println(b.value);
    }
}
