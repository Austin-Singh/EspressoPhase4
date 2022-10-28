// Output:
// From A:
// 15
// From AA:
// 20

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
    A() {}

    int a;
    A(int a) {
	this.a = a;
    }

    public void bar() {
	Io.println("From A:");
	Io.println(a);
    }
} 

class AA extends A {
    int b;
    public AA() {
	b = 89;
    }

    AA(int a) {
	super(a+10);
	b = a;
    }

    public void bar() {
	int a;
	super.bar();

	a = b + this.a; 
	Io.println("From AA:");
	Io.println(a);
    }

    private AA(String s) {
    }
    void foo() {
	AA aa = new AA();
	AA aaa = new AA(5);
	A a = new A();

	AA a2 = new AA("Hello");
	aaa.bar();
    }
    public static void main() {
	new AA().foo();
    }

}


 
