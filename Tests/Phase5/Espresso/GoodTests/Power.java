// Output: 
// 256
// 3125
// 10000000
// Result: 10003381   
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

class Power {
    // power 1
    int p1(int m, int n) {
	if (n==0) {
	    return 1;
	} else {
	    return m * p1(m,n-1);
	}
    }
    

    // power 2
    int p2_h(int m, int n, int acc) {
	if (n==0) {
	    return acc;
	} else {
	    return p2_h(m,n-1,m*acc);
	}
    }
    
    int p2(int m, int n) {
	return p2_h(m,n,1);
    }

    // power 3
    int square(int n) {
	return n*n;
    }
    
    boolean even(int n) {
	return (n%2 == 0);
    }

    int p3(int m, int n) {

	if (n==0){
	    return 1;
	}
	else {
	    if (even(n)) {
		return square(p3(m,n/2));
	    } else {

		return m*square(p3(m,(n-1)/2));
		
	    }
	}
    }
}

class Main {
    Main() {
    }

    public static void main() {
	Power p = new Power();
	int p1,p2,p3;
	p1 = p.p1(2,8);
	Io.println(p1);
	p2 = p.p2(5,5);
	Io.println(p2);
	p3 = p.p3(10,7);
	Io.println(p3);
	
	Io.println(p1+p2+p3);
    }
}
