//(1)
//
//12544
import System;

class Main {
    Main() {
    }
    public static void main(String args[]) {
	int i,a;
	a=0;
	for (i=0;i<1000;i++) {
	    if (i%2 == 0) 
	    	continue;
	    a=a+i;
	    if (a>12345)
	    	break;
	    
	}
	System.out.println(a);
    }
}
