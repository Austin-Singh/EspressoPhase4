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

public class Main {
    private static final char hareChar = 'H';
    private static final char tortChar = 'T';
    private static final int courseLength = 70;
    public static int max(int a, int b) {
	if (a > b)
	    return a;
	return b;
    }
    public static int min(int a, int b) {
	if (a < b)
	    return a;
	return b;
    }
    public static void main() {
	Io.println("Enter a random number to seed the generator: ");
	Random r = new Random(Io.readInt());
	
	Io.println("BANG !!!!!");
	Io.println("AND THEY'RE OFF !!!!!");
	
	Tortoise t = new Tortoise();
	Hare h = new Hare();
	
	for (;;) {
	    int tPos = t.getPosition() + t.move(r.nextInt());
	    int hPos = h.getPosition() + h.move(r.nextInt());
	    
	    tPos = min(tPos, courseLength - 1); //prevent positions from leaving course
	    tPos = max(tPos, 0);
	    
	    hPos = min(hPos, courseLength - 1);
	    hPos = max(hPos, 0);
	    
	    t.setPosition(tPos);
	    h.setPosition(hPos);
	    GeneratePicture(hPos, tPos);
	    
	    if (hPos == courseLength - 1) {
		if (hPos == tPos) {		
		    Io.println("It's a tie.");
		}
		else {
		    Io.println("Hare wins.  Yuck.");
		}
		break;
	    }
	    if (tPos == courseLength - 1) {
		Io.println("TORTOISE WINS!!! YAY!!!");
		break;
	    }
	    //for (int x = 0; x <100000; x++) { }//introduce a delay 
	}
    }
    public static void GeneratePicture(int harePos, int tortPos) {
	int ouch = 0;
	int min;
	int max;
	char minChar;
	char maxChar;
	if (harePos < tortPos) {
	    min = harePos;
	    max = tortPos;
	    minChar = hareChar;
	    maxChar = tortChar;
	} else {
	    min = tortPos;
	    max = harePos;
	    minChar = tortChar;
	    maxChar = hareChar;
	}
	for (int x = 0; x < min; x++) {
	    Io.print("-");
	}
	if (min == max) {
	    Io.print("OUCH!!!");
	    ouch = 1;
	} else {
	    Io.print(minChar);
	}
	if (min != max) {
	    for (int x = min + 1; x < max; x++) {
		Io.print("-");
	    }
	    Io.print(maxChar);
	}
	for (int x = max + 1; x < courseLength-(ouch*6); x++) {
	    Io.print("-");
	}
	Io.println("");
    }
}
class Tortoise {
    private int position;
    
    public Tortoise(){
	position = 0;
    }
    public int getPosition(){
	return position;
    }
    public void setPosition(int p){
	position = p;
    }
    public int move(int rand){
	if (rand < 0)
	    rand = -rand;
	
	rand %= 10;
	
	if (rand <= 4)
	    return 3; //fast plod (0, 1, 2, 3, 4)
	if (rand <= 6)
	    return -6; //slip (5, 6)
	else
	    return 1; //slow plod (7, 8, 9)
    }
}

class Hare {
    private int position;
    
    public Hare() {
	position = 0;
    }
    public int getPosition() {
	return position;
    }
    public void setPosition(int p){
	position = p;
    }
    public int move(int rand) {
	if (rand < 0)
	    rand = -rand;
	
	rand %= 10;
	
	if (rand <= 1)
	    return 0;  //sleep (0, 1)
	if (rand <= 3)
	    return 9;	//big hop (2, 3)
	if (rand <= 4)
	    return -12; //big slip (4)
	if (rand <= 7)
	    return 1;  //small hop (5, 6, 7)
	else
	    return -2;  //small slip (8, 9);
    }
}

class Random {
    private static final int A = 48271;
    private static final int M = 2147483647;
    
    private static final int Q = 44488; // = M / A
    private static final int R = 3399; // = M % A
    
    private int seed;
    
    public Random(int s) {
	if (s < 0)
	    s += M;
	seed = (s == 0) ? 1 : s;
    }
    
    public int nextInt() {
	return seed = (A * seed) % M;
    }
}
