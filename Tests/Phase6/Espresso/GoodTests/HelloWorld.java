//(1)
//
//hello world
import Random;
import System;

class HelloWorld {
    public static void main(String args[]) {
	randomString(-229985452);
	System.out.print(' ');
	randomString(-147909649);
	System.out.println("");    
    }
    
    public static void randomString(int seed) {
	Random rand = new Random(seed);
	for(int i=0;;i++) {
	    int n = rand.nextInt(27);
	    if (n == 0) break;
	    char c =(char)( '`' + n);
	    System.out.print(c);
	}
    }
}