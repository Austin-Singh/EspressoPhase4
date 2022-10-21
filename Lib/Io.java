import java.io.*;
import java.lang.Integer;
import java.lang.Double;

class Io {
    static BufferedReader in = new BufferedReader(new InputStreamReader(java.lang.System.in));
    
    static public void print(byte b)  { java.lang.System.out.print(b); }
    static public void print(short s) { java.lang.System.out.print(s); }
    static public void print(char c)  { java.lang.System.out.print(c); }
    static public void print(int i)   { java.lang.System.out.print(i);}
    static public void print(long l)  { java.lang.System.out.print(l);}
    static public void print(float f) { java.lang.System.out.print(f);}
    static public void print(double d){ java.lang.System.out.print(d);}
    static public void print(java.lang.String s){ java.lang.System.out.print(s);}
    static public void print(boolean b){ java.lang.System.out.print(b);}
    static public void print(Object o){ java.lang.System.out.print(o);}
    static public void println(byte b) { java.lang.System.out.println(b); }
    static public void println(short s){ java.lang.System.out.println(s); }
    static public void println(char c) { java.lang.System.out.println(c);}
    static public void println(int i)  { java.lang.System.out.println(i);}
    static public void println(long l) { java.lang.System.out.println(l);}
    static public void println(float f){ java.lang.System.out.println(f);}
    static public void println(double d){ java.lang.System.out.println(d); }
    static public void println(java.lang.String s){ java.lang.System.out.println(s); }
    static public void println(boolean b){ java.lang.System.out.println(b); }
    static public void println(Object o){ java.lang.System.out.println(o);}

    static public int readInt() throws IOException { 
	return Integer.parseInt(in.readLine());
    }
    static public long readLong() throws IOException { 
	return Long.parseLong(in.readLine());
    }
    static public float readFloat() throws IOException  { 
	return Float.parseFloat(in.readLine()); 
    }
    static public double readDouble() throws IOException  { 
	return Double.parseDouble(in.readLine());
    }
    static public String readString() throws IOException  { 
	return in.readLine();
    }
}

