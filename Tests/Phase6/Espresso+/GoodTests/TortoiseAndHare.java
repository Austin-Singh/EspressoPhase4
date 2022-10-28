//(28)
//0
//Enter a random number to seed the generator: BANG !!!!!
//AND THEY'RE OFF !!!!!
//-H-T------------------------------------------------------------------
//--H-T-----------------------------------------------------------------
//T--H------------------------------------------------------------------
//-T----------H---------------------------------------------------------
//T------------H--------------------------------------------------------
//---T------------------H-----------------------------------------------
//----T---------------H-------------------------------------------------
//-----T---------------H------------------------------------------------
//------T--------------H------------------------------------------------
//-------T-----------H--------------------------------------------------
//--------T-------------------H-----------------------------------------
//--T--------------------------H----------------------------------------
//-----T--------------------------------H-------------------------------
//--------T---------------------------H---------------------------------
//---------T-----------------------------------H------------------------
//----------T-----------------------------------H-----------------------
//-----------T-----------------------------------H----------------------
//------------T-----------------------------------H---------------------
//-------------T-----------------------------------H--------------------
//--------------T-------------------------------------------H-----------
//--------T--------------------------------------------------H----------
//---------T-------------------------------------------------H----------
//------------T--------------------------------------------H------------
//---------------T--------------------------------------------------H---
//------------------T--------------------------------------------------H
//Hare wins.  Yuck.
import System;

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
    public static void main(String args[]) {
	System.out.print("Enter a random number to seed the generator: ");
	RandomGen r = new RandomGen(System.out.readInt());
	
	System.out.println("BANG !!!!!");
	System.out.println("AND THEY'RE OFF !!!!!");
	
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
		    System.out.println("It's a tie.");
		}
		else {
		    System.out.println("Hare wins.  Yuck.");
		}
		break;
	    }
	    if (tPos == courseLength - 1) {
		System.out.println("TORTOISE WINS!!! YAY!!!");
		break;
	    }
	    for (int x = 0; x <100; x++) { }//introduce a delay 
	}
    }
    public static void GeneratePicture(int harePos, int tortPos) {
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
	    System.out.print("-");
	}
	if (min == max) {
	    System.out.print("OUCH!!!");
	} else {
	    System.out.print(minChar);
	}
	if (min != max) {
	    for (int x = min + 1; x < max; x++) {
		System.out.print("-");
	    }
	    System.out.print(maxChar);
	}
	for (int x = max + 1; x < courseLength; x++) {
	    System.out.print("-");
	}
	System.out.println("");
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

class RandomGen {
    private static final int A = 48271;
    private static final int M = 2147483647;
    
    private static final int Q = 44488; // = M / A
    private static final int R = 3399; // = M % A
    
    private int seed;
    
    public RandomGen(int s) {
	if (s < 0)
	    s += M;
	seed = (s == 0) ? 1 : s;
    }
    
    public int nextInt() {
	return seed = (A * seed) % M;
    }
}
