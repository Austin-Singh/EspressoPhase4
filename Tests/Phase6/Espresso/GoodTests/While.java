//(1)
//
//65
import System;

class Main {
    public static void main(String args[]) {
	int a,b,c;
	a = 10;
	b = 0;
	c = 0;
	while (a>0) {
	    b = b + a;
	    c++;
	    a--;
	}
	System.out.println(a+b+c);
    }
}
