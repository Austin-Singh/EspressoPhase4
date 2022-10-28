// Output: 12

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

public class GoodSwitch {
    
    public static void main() {
	int a = 1;
	
	switch (a) {
	case 1: 
	    a++;
	    for (int i =0; i < 10; i++)
		a++;
	    break;
	case 3:   
	    a--;  
	    break;
	case 4:   
	    a++;  
	    break;
	}
        Io.println(a);
    }
}
