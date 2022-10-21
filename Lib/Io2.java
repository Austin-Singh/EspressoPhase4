import java.io.*;
import java.lang.Integer;
import java.lang.Double;

class Io2 {
     BufferedReader in = new BufferedReader(new InputStreamReader(java.lang.System.in));
    
     public void print(byte b)  { java.lang.System.out.print(b); }
     public void print(short s) { java.lang.System.out.print(s); }
     public void print(char c)  { java.lang.System.out.print(c); }
     public void print(int i)   { java.lang.System.out.print(i);}
     public void print(long l)  { java.lang.System.out.print(l);}
     public void print(float f) { java.lang.System.out.print(f);}
     public void print(double d){ java.lang.System.out.print(d);}
     public void print(String s){ java.lang.System.out.print(s);}
     public void print(boolean b){ java.lang.System.out.print(b);}
     public void println(byte b) { java.lang.System.out.println(b); }
     public void println(short s){ java.lang.System.out.println(s); }
     public void println(char c) { java.lang.System.out.println(c);}
     public void println(int i)  { java.lang.System.out.println(i);}
     public void println(long l) { java.lang.System.out.println(l);}
     public void println(float f){ java.lang.System.out.println(f);}
     public void println(double d){ java.lang.System.out.println(d); }
     public void println(String s){ java.lang.System.out.println(s); }
     public void println(boolean b){ java.lang.System.out.println(b); }

     public int readInt() throws IOException { 
	return Integer.parseInt(in.readLine());
    }
     public long readLong() throws IOException { 
	return Long.parseLong(in.readLine());
    }
     public float readFloat() throws IOException  { 
	return Float.parseFloat(in.readLine()); 
    }
     public double readDouble() throws IOException  { 
	return Double.parseDouble(in.readLine());
    }
     public String readString() throws IOException  { 
	return in.readLine();
    }
}

