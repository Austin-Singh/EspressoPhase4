// Output:
// 7
// 9
// 11
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

class test {
    int a = 7;
    test () {}
    int t1() { return a; }
}
class test2 {
    int b = 9;
    int t1() { return b; }
}

class test3 {
    int c;
    int t1() { c=11; return c; }
}

class Main {
    public static void main() {
	Io.println(new test().t1());
	Io.println(new test2().t1());
	Io.println(new test3().t1());
    }
}
