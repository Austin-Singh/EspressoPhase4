//(1)
//
//49950
import System;

class Main {
    public static void main(String args[]) {
	int c = 0;
	for (int i=0; i<100; i++) {
	    for (int j=0; j<100; j=j+1, j=j-1, j++) {
		int k = 10;
		while (k > 0) {
		    k = (k--) - 1;
		    c = c - k;
		}
		c = c + j;
	    }
	    c=c+i;
	}
	System.out.println(c);
    }
}
